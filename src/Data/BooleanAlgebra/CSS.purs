module Data.BooleanAlgebra.CSS where

import Prelude

import Control.Alt ((<|>))
import Control.Bind (bindFlipped)
import Control.Comonad (extract)
import Control.MonadPlus (class MonadPlus, empty, guard)
import Data.Array (filter, mapWithIndex)
import Data.BooleanAlgebra.NormalForm (NormalForm, toArrays, free)
import Data.Foldable (all, foldMap, foldl, oneOfMap)
import Data.FoldableWithIndex (foldMapWithIndex, foldlWithIndex)
import Data.HeytingAlgebra (ff, tt)
import Data.InterTsil (InterTsil(..), concat)
import Data.Lens (Iso', iso)
import Data.Map (Map, singleton, unionWith)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, un, unwrap)
import Data.Set as Set
import Data.String (joinWith)
import Data.Symbol (class IsSymbol)
import Data.Traversable (class Foldable, sequence)
import Data.Tuple (Tuple(..))
import Prim.Row as Row
import Prim.RowList (class RowToList, Cons, Nil, RowList)
import Record (get, insert)
import Type.Proxy (Proxy(..))
import Type.RowList (class ListToRow)

-- | A single portion of a selector. Covers atoms such as matching an element
-- | or class.
data Select
  = Element String
  | Class String
  | PseudoCls String
  | PseudoEl String
  | Attribute AttrMatch

derive instance eqSelect :: Eq Select
derive instance ordSelect :: Ord Select

data Relation
  = Child
  | Descendant
  | Next -- posterus
  | Later -- posterior

derive instance eqRelation :: Eq Relation
derive instance ordRelation :: Ord Relation

newtype Rel = Rel { vertical :: Boolean, immediate :: Boolean }

derive instance eqRel :: Eq Rel
derive instance ordRel :: Ord Rel

rel :: Iso' Relation Rel
rel = iso from to where
  from = case _ of
    Child      -> Rel { vertical: true,  immediate: true }
    Descendant -> Rel { vertical: true,  immediate: false }
    Next       -> Rel { vertical: false, immediate: true }
    Later      -> Rel { vertical: false, immediate: false }
  to = case _ of
    Rel { vertical: true,  immediate: true }  -> Child
    Rel { vertical: true,  immediate: false } -> Descendant
    Rel { vertical: false, immediate: true }  -> Next
    Rel { vertical: false, immediate: false } -> Later

-- | An attribute name and specifics about how to match it, where `Nothing`
-- | means it simply must exist.
newtype AttrMatch = AttrMatch
  { attr :: String
  , match :: Maybe MatchValue
  }

derive instance eqAttrMatch :: Eq AttrMatch
derive instance ordAttrMatch :: Ord AttrMatch

-- | Specifics about how to match the value of an attribute.
newtype MatchValue = MatchValue
  { matchType :: MatchValueType
  , value :: String
  , insensitive :: Boolean
  }

derive instance eqMatchValue :: Eq MatchValue
derive instance ordMatchValue :: Ord MatchValue

-- | The type of match, exact or contains, etc.
data MatchValueType
  = Exact -- [attr=value]
  | ListContains -- [attr~=value]
  | Contains -- [attr*=value]
  | StartsWith -- [attr^=value]
  | EndsWith -- [attr$=value]
  | LangCode -- [attr|=value]

derive instance eqMatchValueType :: Eq MatchValueType
derive instance ordMatchValueType :: Ord MatchValueType

-- | A full CSS selector represented as a free boolean algebra over the
-- | selector atoms.
-- S.Map (InterList Relation (M.Map Select Boolean)) Boolean
newtype Selector = S (NormalForm Select)
derive instance newtypeSelector :: Newtype Selector _
derive newtype instance heytingAlgebrCSSelector :: HeytingAlgebra Selector
derive newtype instance booleanAlgebrCSSelector :: BooleanAlgebra Selector
derive newtype instance eqSelector :: Eq Selector
derive newtype instance ordSelector :: Ord Selector
instance showSelector :: Show Selector where
  show = un S >>> fromNF >>> print

-- | Match an element.
element :: String -> Selector
element = S <<< free <<< Element

-- | Match a list of classes.
classes :: Array String -> Selector
classes = all (S <<< free <<< Class)

-- | A pseudo-class.
pseudo :: String -> Selector
pseudo = S <<< free <<< PseudoCls

-- | Pseudo elements.
pseudoElement :: String -> Selector
pseudoElement = S <<< free <<< PseudoEl

-- | Match anything and everything!
anything :: Selector
anything = tt

-- | Match nothing ...
nothing :: Selector
nothing = ff

-- | Match a `<div>` element.
div :: Selector
div = element "div"

-- | Matches when an element is hovered over.
hover :: Selector
hover = pseudo "hover"

-- | Matches the pseudo-element `::before` the given element.
before :: Selector -> Selector
before = conj $ pseudoElement "before"

-- | Matches the pseudo-element `::after` the given element.
after :: Selector -> Selector
after = conj $ pseudoElement "after"

-- | Match an element that has this attribute.
attrExists :: String -> Selector
attrExists attr = S $ free $ Attribute $ AttrMatch
  { attr, match: Nothing }

-- | Match an element wtih an attribute having this value.
exactAttr :: String -> String -> Selector
exactAttr a v = attrValue a $ MatchValue
  { matchType: Exact
  , value: v
  , insensitive: false
  }

-- | More general matching, see `MatchValue` for specifics.
attrValue :: String -> MatchValue -> Selector
attrValue a v = S $ free $ Attribute $ AttrMatch { attr: a, match: Just v }

newtype Single a = Single (Maybe { inverted :: Boolean, value :: a })
derive instance newtypeSingle :: Newtype (Single a) _
instance eqSingle :: Eq a => Eq (Single a) where
  eq (Single (Just a)) (Single (Just b)) =
    a.inverted == b.inverted && a.value == b.value
  eq (Single Nothing) (Single Nothing) = true
  eq _ _ = false
instance showSingle :: Show a => Show (Single a) where
  show (Single Nothing) = "neutral"
  show (Single (Just { inverted, value })) =
    (if inverted then "!" else "") <> show value

newtype Several a = Several (Map a Boolean)
derive instance newtypeSeveral :: Newtype (Several a) _
derive newtype instance eqSeveral :: Ord a => Eq (Several a)

-- A single (conjunctive) selector
type ASelector =
  { element   :: Single  String
  , classes   :: Several String
  , pseudoCls :: Several String
  , attrs     :: Several AttrMatch
  , pseudoEl  :: Single String
  }
newtype Atom = Atom ASelector
derive instance newtypeAtom :: Newtype Atom _
derive instance eqAtom :: Eq Atom

-- | A class for expressing types that express quasi conjunctive (or
-- | disjunctive) clauses in a more structured way than `Free`.
-- |
-- | Laws:
-- |   - identity: `combine a neutral = pure a = combine neutral a`
-- |   - idempotence: `combine a a = pure a`
-- |   - commutativity: `combine a b` has the same elements as `combine b a`
-- |   - associativity: `combine a =<< combine b c` has the same elements as
-- |                    `combine a b >>= (combine <@> c)`

-- fun fact: īdem (m.) eadem (f.) idem (n.) means “the same” in Latin
class Combinatorial c where
  combine :: forall f. MonadPlus f => c -> c -> f c
  neutral :: c

-- subsumes a a == E
-- (subsumes a neutral) = if a == neutral then E else LSR
-- subsumes a b == LSR && subsumes b c == LSR => subsumes a c == LSR
-- (subsumes a b == LSR) = (subsumes b a == RSL)
-- else (for E, T, I): subsumes a b = subsumes b a
class (Eq c, Combinatorial c) <= Subsumes c where
  subsumes :: c -> c -> S

data S
  -- they are equal: a == b, or a <=> b
  = E
  -- left subsumes right: a || b == a, or a => b
  | LSR
  -- right subsumes left: a || b == b, or b => a
  | RSL
  -- their disjunction is a tautology: a || b == tt
  | T
  -- independent
  | I
instance showS :: Show S where
  show E = "Equal"
  show LSR = "Left subsumes right"
  show RSL = "Right subsumes left"
  show T = "Complementary"
  show I = "Independent"

-- commutative
instance semigroupS :: Semigroup S where
  -- strongly annihilate
  append T _ = T
  append _ T = T
  -- weakly annihilate
  append I _ = I
  append _ I = I
  -- identity
  append E s = s
  append s E = s
  -- complements
  append LSR LSR = LSR
  append RSL RSL = RSL
  append LSR RSL = I
  append RSL LSR = I

instance monoidS :: Monoid S where
  mempty = E

data ReSult c = Taut | Uno c | Duo c c
instance showReSult :: Show c => Show (ReSult c) where
  show Taut = "[]"
  show (Uno c) = show [c]
  show (Duo c1 c2) = show [c1, c2]

subsume :: forall c. Subsumes c => c -> c -> ReSult c
subsume a b = case subsumes a b of
  T -> Taut
  I -> Duo a b
  LSR -> Uno a
  _ -> Uno b

subsumptite :: forall c. Subsumes c => Array c -> Array c
subsumptite elements = finally $ foldlWithIndex f (Just mempty) elements where
  f _ Nothing _ = Nothing
  f i (Just removed) c1 =
    let
      subres = foldlWithIndex g (Just mempty) elements
      g _ Nothing _ = Nothing
      g j (Just more) c2 = case subsumes c1 c2 of
        LSR -> Just (Set.insert j more)
        E | j > i -> Just (Set.insert j more)
        T -> Nothing
        _ -> Just more
    in subres <#> \more -> removed <> more
  finally Nothing = []
  finally (Just removed) = map extract $ elements # mapWithIndex Tuple # filter
    \(Tuple e _) -> not Set.member e removed

boolean :: forall c. Subsumes c => Array (Array c) -> Array c
boolean = subsumptite <<< bindFlipped combineFold

instance combinatorialRecord ::
  ( RowToList r rl
  , CombinatorialRL rl r r
  ) => Combinatorial (Record r) where
    combine = combineRL (Proxy :: Proxy rl)
    neutral = neutralRL (Proxy :: Proxy rl) (Proxy :: Proxy r)

-- Conjoin many conjunctive clauses together, doing case analysis as necesssary
-- or dropping impossible conjunctions.
combineFold ::
  forall f g c.
    Combinatorial c =>
    Foldable f => MonadPlus g =>
  f c -> g c
combineFold = foldl (\fb a -> fb >>= \b -> combine b a) (pure neutral)

combine3 :: forall f c. Combinatorial c => MonadPlus f => c -> c -> c -> f c
combine3 a b c = combine a b >>= combine c -- combine a b >>= (combine <@> c)

class ListToRow rl r <= CombinatorialRL (rl :: RowList Type) (rr :: Row Type) (r :: Row Type) | rl -> r where
  combineRL :: forall f. MonadPlus f => Proxy rl -> Record rr -> Record rr -> f (Record r)
  neutralRL :: Proxy rl -> Proxy rr -> Record r

instance combNil :: CombinatorialRL Nil rr () where
  combineRL _ _ _ = pure {}
  neutralRL _ _ = {}
instance combCons ::
  ( IsSymbol s
  , Combinatorial t
  , CombinatorialRL rl rr r
  , Row.Cons s t r r'
  , Row.Lacks s r
  , Row.Cons s t ignored rr
  ) => CombinatorialRL (Cons s t rl) rr r' where
    combineRL _ r1 r2 = insert s
      <$> combine (get s r1) (get s r2)
      <*> ofRecordr (combineRL (Proxy :: Proxy rl) r1 r2)
      where
        ofRecordr = identity :: forall f. f (Record r) -> f (Record r)
        s = Proxy :: Proxy s
    neutralRL _ rp = insert (Proxy :: Proxy s) neutral (neutralRL (Proxy :: Proxy rl) rp :: Record r)

instance combinatorialUnit :: Combinatorial Unit where
  combine _ _ = pure neutral
  neutral = unit
instance subsumesUnit :: Subsumes Unit where
  subsumes _ _ = E

derive newtype instance combinatorialAtom :: Combinatorial Atom

{-
a = single.mk "a"
_a = single.inv a
b = single.mk "b"
_b = single.inv b
-}
single :: { mk :: forall a. a -> Single a, inv :: forall a. Single a -> Single a }
single =
  { mk: \value -> Single (Just { inverted: false, value })
  , inv: case _ of
      Single Nothing -> Single Nothing
      Single (Just { inverted, value }) ->
        Single (Just { inverted: not inverted, value })
  }

instance combinatorialSingle :: Eq a => Combinatorial (Single a) where
  neutral = Single Nothing
  combine l@(Single (Just a)) r@(Single (Just b)) =
    case a.inverted, b.inverted of
      -- x && !x == ff
      -- l && !r == l
      false, true | a.value /= b.value -> pure l
                  | otherwise -> empty
      -- !x && x == ff
      -- !l && r == r
      true, false | a.value /= b.value -> pure r
                  | otherwise -> empty
      -- x && x == x
      -- y && z == ff (y /= z)
      _, _ | a.value == b.value -> pure l
           | otherwise -> empty
  combine (Single Nothing) v = pure v
  combine v (Single Nothing) = pure v
instance subsumesSingle :: Eq a => Subsumes (Single a) where
  subsumes (Single l) (Single r) = case l, r of
    Nothing, Nothing -> E
    Just _, Nothing -> RSL
    Nothing, Just _ -> LSR
    Just a, Just b
      | a.value == b.value ->
        if a.inverted == b.inverted
          then E
          else T
      | otherwise -> I

instance combinatorialSeveral :: Ord a => Combinatorial (Several a) where
  neutral = Several empty
  combine (Several a) (Several b) =
    oneOfMap (pure <<< Several) $ sequence $
      unionWith agreement (a <#> Just) (b <#> Just)
    where
      agreement (Just false) (Just false) = Just false
      agreement (Just true) (Just true) = Just true
      agreement _ _ = Nothing

newtype Related a = Related (InterTsil Boolean a)
derive instance newtypeRelated :: Newtype (Related a) _
derive newtype instance eqRelated :: Eq a => Eq (Related a)

instance combinatorialRelated :: Combinatorial a => Combinatorial (Related a) where
  neutral = Related (One neutral)
  combine (Related a) (Related b) = Related <$> inner a b where
    inner = case _, _ of
      One s1, One s2 ->
        One <$> combine s1 s2
      One s1, More more rel s2 ->
        More more rel <$> combine s1 s2
      More more rel s1, One s2 ->
        More more rel <$> combine s1 s2
      More m1 r1 s1, More m2 r2 s2 ->
        let
          options =
            inner m1 m2
            <|> trySlide m1 r1 m2
            <|> trySlide m2 r2 m1
        in More <$> options <@> (r1 && r2) <*> combine s1 s2

    trySlide m1 true m2 = slide m1 m2
    trySlide _ false _ = empty

    slide m1 = go where
      go (One s2) = pure (More m1 true s2)
      go (More m2 r2 s2) =
        let
          btwn = guard r2 *> inner m1 (More m2 true neutral)
          rest = inner m1 m2 <|> go m2
        in More <$> (btwn <|> rest) <@> r2 <@> s2

instance subsumesRelated :: Subsumes a => Subsumes (Related a) where
  subsumes (Related a) (Related b) = case a, b of
    One s1, One s2 -> subsumes s1 s2
    One s1, More m2 r2 s2 -> LSR <> subsumes s1 s2
    More m1 r1 s1, One s2 -> RSL <> subsumes s1 s2
    More m1 r1 s1, More m2 r2 s2 ->
      subsumes (Related m1) (Related m2) <>
      subsumes s1 s2 <>
      case r1, r2 of
        true, false -> LSR
        false, true -> RSL
        _, _ -> mempty

type Horiz = Related Atom
type Vert = Related Horiz

final :: forall a. a -> Related a
final = Related <<< One
imm :: forall a. Related a -> a -> Related a
imm (Related m) s = Related (More m false s)
dist :: forall a. Related a -> a -> Related a
dist (Related m) s = Related (More m true s)

appR :: forall a. Related a -> Boolean -> Related a -> Related a
appR (Related m1) r (Related m2) = Related (concat m1 r m2)

printHoriz :: Horiz -> String
printHoriz (Related (One s)) = print1 s
printHoriz (Related (More m r s)) = printHoriz (Related m) <> (if r then " ~ " else " + ") <> print1 s

printVert :: Vert -> String
printVert (Related (One h)) = printHoriz h
printVert (Related (More m r h)) =
  printVert (Related m)
  <> (if r then " " else " > ")
  <> printHoriz h

-- A disjunction of Several selectors
type SomeSelectors = Array Atom

-- Identity selector
matchAll' :: ASelector
matchAll' =
  { element: neutral
  , classes: neutral
  , pseudoCls: neutral
  , pseudoEl: neutral
  , attrs: neutral
  }
matchAll = Atom matchAll' :: Atom

matchElement :: String -> Atom
matchElement = matchElement' false
matchClass :: String -> Atom
matchClass = matchClass' false
matchPseudoCls :: String -> Atom
matchPseudoCls = matchPseudoCls' false
matchPseudoEl :: String -> Atom
matchPseudoEl = matchPseudoEl' false
matchAttr :: AttrMatch -> Atom
matchAttr = matchAttr' false

matchElement' :: Boolean -> String -> Atom
matchElement' inverted name = Atom $ matchAll'
  { element = Single $ Just { inverted, value: name } }

matchClass' :: Boolean -> String -> Atom
matchClass' inverted name = Atom $ matchAll'
  { classes = Several $ singleton name inverted }

matchPseudoCls' :: Boolean -> String -> Atom
matchPseudoCls' inverted name = Atom $ matchAll'
  { pseudoCls = Several $ singleton name inverted }

matchPseudoEl' :: Boolean -> String -> Atom
matchPseudoEl' inverted name = Atom $ matchAll'
  { pseudoEl = Single $ Just { inverted, value: name } }

matchAttr' :: Boolean -> AttrMatch -> Atom
matchAttr' inverted match = Atom $ matchAll'
  { attrs = Several $ singleton match inverted }

selectToMatch :: Select -> Atom
selectToMatch = selectToMatch' <<< (Tuple <@> false)

selectToMatch' :: Tuple Select Boolean -> Atom
selectToMatch' (Tuple v i) = case v of
  Element s -> matchElement' i s
  Class s -> matchClass' i s
  PseudoCls s -> matchPseudoCls' i s
  PseudoEl s -> matchPseudoEl' i s
  Attribute s -> matchAttr' i s

fromNF :: NormalForm Select -> SomeSelectors
fromNF = not not >>> unwrap >>> toArrays >=> map selectToMatch' >>> combineFold

ensure :: String -> String -> String
ensure s "" = s
ensure _ s = s

-- An empty string means false, which we represent with :not(*)
print :: SomeSelectors -> String
print = ensure ":not(*)" <<< joinWith ", " <<< map print1

print1 :: Atom -> String
print1 (Atom v) = ensure "*" $ e <> as <> c <> pc <> pe where
  invert false n = n
  invert true n = ":not(" <> n <> ")"
  -- Print the element, or *
  e = case v.element of
    Single Nothing -> ""
    Single (Just { inverted, value }) ->
      invert inverted value
  -- Print attributes in brackets[]
  as = v.attrs # unwrap # foldMapWithIndex \(AttrMatch { attr, match }) i ->
    invert i case match of
      Nothing -> "[" <> attr <> "]"
      Just (MatchValue { matchType, value, insensitive }) ->
        let
          i' = if insensitive then " i" else ""
          op = case matchType of
            Exact -> ""
            ListContains -> "~"
            Contains -> "*"
            StartsWith -> "^"
            EndsWith -> "$"
            LangCode -> "|"
        in "[" <> attr <> op <> "=" <> show value <> i' <> "]"
  -- Print classes, preceded by periods.
  c = v.classes # unwrap # foldMapWithIndex \name i ->
    invert i ("." <> name)
  -- Print pseudo-classes, preceded by colons:
  pc = v.pseudoCls # unwrap # foldMapWithIndex \name i ->
    invert i (":" <> name)
  -- Print the pseudo-element (if applicable), preceded by a double colon::
  pe = v.pseudoEl # unwrap # foldMap \{ inverted, value } ->
    invert inverted ("::" <> value)

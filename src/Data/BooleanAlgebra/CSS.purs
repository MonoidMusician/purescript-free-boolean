module Data.BooleanAlgebra.CSS where

import Prelude

import Control.Alt ((<|>))
import Control.Alternative (class Alternative, empty)
import Control.Apply (lift5)
import Control.MonadZero (guard)
import Data.Array (drop, mapMaybe)
import Data.Bifoldable (class Bifoldable, bifoldMap, bifoldl, bifoldlDefault, bifoldr, bifoldrDefault)
import Data.Bifunctor (class Bifunctor, bimap, rmap)
import Data.Bitraversable (class Bitraversable, bisequenceDefault, bitraverse)
import Data.BooleanAlgebra.NormalForm (NormalForm, toArrays, free)
import Data.Foldable (class Foldable, all, foldM, foldMap, foldl, oneOfMap)
import Data.FoldableWithIndex (foldMapWithIndex)
import Data.HeytingAlgebra (ff, tt)
import Data.Lens (Iso', iso)
import Data.Map (Map, singleton, unionWith)
import Data.Maybe (Maybe(..))
import Data.Monoid (mempty)
import Data.Newtype (class Newtype, un, unwrap)
import Data.Semigroup.Foldable (class Foldable1, fold1Default, foldMap1)
import Data.Semigroup.Traversable (class Traversable1, sequence1Default, traverse1)
import Data.String (joinWith)
import Data.Traversable (class Traversable, sequence)
import Data.Tuple (Tuple(..))

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

-- A single (conjunctive) selector
type ASelector =
  { element :: Maybe
    { inverted :: Boolean
    , name :: String
    }
  , classes :: Map String Boolean
  , pseudoCls :: Map String Boolean
  , pseudoEl :: Maybe
    { inverted :: Boolean
    , name :: String
    }
  , attrs :: Map AttrMatch Boolean
  }
newtype Atom = Atom ASelector
derive instance newtypeAtom :: Newtype Atom _

data InterTsil a b = One b | More (InterTsil a b) a b

instance functorInterTsil :: Functor (InterTsil a) where
  map = rmap
instance bifunctorInterTsil :: Bifunctor InterTsil where
  bimap _ g (One b) = One (g b)
  bimap f g (More m a b) = More (bimap f g m) (f a) (g b)

instance foldable1InterTsil :: Foldable1 (InterTsil a) where
  foldMap1 g (One b) = g b
  foldMap1 g (More m _ b) = foldMap1 g m <> g b
  fold1 x = fold1Default x
instance foldableInterTsil :: Foldable (InterTsil a) where
  foldMap = bifoldMap mempty
  foldl = bifoldl pure
  foldr = bifoldr (flip pure)
instance bifoldableInterTsil :: Bifoldable InterTsil where
  bifoldMap _ g (One b) = g b
  bifoldMap f g (More m a b) = bifoldMap f g m <> f a <> g b
  bifoldl x = bifoldlDefault x
  bifoldr x = bifoldrDefault x

instance traversable1InterTsil :: Traversable1 (InterTsil a) where
  traverse1 g (One b) = One <$> g b
  traverse1 g (More m a b) = More <$> traverse1 g m <@> a <*> g b
  sequence1 x = sequence1Default x
instance traversableInterTsil :: Traversable (InterTsil a) where
  traverse = bitraverse pure
  sequence = bitraverse pure id
instance bitraversableInterTsil :: Bitraversable InterTsil where
  bitraverse _ g (One b) = One <$> g b
  bitraverse f g (More m a b) = More <$> bitraverse f g m <*> f a <*> g b
  bisequence x = bisequenceDefault x

type Selectree = InterTsil Relation ASelector

last :: forall a b. InterTsil a b -> b
last (One s) = s
last (More _ _ s) = s

class Combinatorial c where
  combine :: c -> c -> Array c
  neutral :: c

instance combinatorialAtom :: Combinatorial Atom where
  combine (Atom a1) (Atom a2) = Atom <$> conjoin a1 a2
  neutral = Atom matchAll

newtype Related a = Related (InterTsil Boolean a)
derive instance newtypeRelated :: Newtype (Related a) _

instance combinatorialRelated :: Combinatorial a => Combinatorial (Related a) where
  neutral = Related (One neutral)
  combine (Related a) (Related b) = Related <$>
    let
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

      trySlide m1 true m2 =
        drop 1 $ slide m1 m2
      trySlide _ false _ = empty

      slide m1 (One s2) =
        inner m1 (One s2) <|> pure (More m1 true s2)
      slide m1 (More m2 r2 s2) =
        inner m1 (More m2 r2 s2) <|> rest where
          btwn = guard r2 *> inner m1 (More m2 true neutral)
          step = slide m1 m2
          rest = More <$> (btwn <|> step) <@> r2 <@> s2
    in inner a b

type Horiz = Related Atom
type Vert = Related Horiz

-- i ~ j ~ k && a ~ b
-- ==
-- a ~ i ~ j ~ kb
-- ai ~ j ~ kb
-- i ~ a ~ j ~ kb : combineH (More (One _i) true matchAll) (One _a) <#> \m ->

-- i ~ aj ~ kb

-- i ~ j ~ a ~ kb

final :: forall a. a -> Related a
final = Related <<< One
imm :: forall a. Related a -> a -> Related a
imm (Related m) s = Related (More m false s)
dist :: forall a. Related a -> a -> Related a
dist (Related m) s = Related (More m true s)

app :: forall a b. InterTsil a b -> a -> InterTsil a b -> InterTsil a b
app m r (One s) = More m r s
app m r (More m1 r1 s) = More (app m r m1) r1 s

appR :: forall a. Related a -> Boolean -> Related a -> Related a
appR (Related m1) r (Related m2) = Related (app m1 r m2)

_i = Atom (matchClass "i") :: Atom
_j = Atom (matchClass "j") :: Atom
_k = Atom (matchClass "k") :: Atom
_l = Atom (matchClass "l") :: Atom
ijk = dist (dist (final _i) _j) _k :: Horiz
_a = Atom (matchClass "a") :: Atom
_b = Atom (matchClass "b") :: Atom
test = combine (ijk) (dist (final _a) _b) :: Array Horiz
tested = map printHoriz test :: Array String
test1 = map printHoriz (combine (dist ijk _l) (dist (final _a) _b)) :: Array String

midTest :: Array Horiz
midTest =
  let
    q = Atom <<< matchClass
    ab = dist (final (q "a")) (q "b")
    cd = dist (final (q "c")) (q "d")
    abcd = appR ab false cd
    wxyz = dist (dist (imm (final (q "w")) (q "x")) (q "y")) (q "z")
  in combine abcd wxyz

-- .a ~ .b > .c .d ~ .e + .f > .g && .h > .i ~ .j ~ .k .l + .m .n
bigTest :: Array Vert
bigTest =
  let
    q = Atom <<< matchClass
    ab = dist (final (q "a")) (q "b")
    c = final (q "c")
    def = imm (dist (final (q "d")) (q "e")) (q "f")
    g = final (q "g")
    h = final (q "h")
    ijk = dist (dist (final (q "i")) (q "j")) (q "k")
    lm = imm (final (q "l")) (q "m")
    n = final (q "n")
    abcdefg = imm (dist (imm (final ab) c) def) g
    hijklmn = dist (dist (imm (final h) ijk) lm) n
  in combine abcdefg hijklmn

bigTested :: Array String
bigTested = map printVert bigTest

bigTests = joinWith " || " bigTested :: String

printHoriz :: Horiz -> String
printHoriz (Related (One (Atom s))) = print1 s
printHoriz (Related (More m r (Atom s))) = printHoriz (Related m) <> (if r then " ~ " else " + ") <> print1 s

printVert :: Vert -> String
printVert (Related (One h)) = printHoriz h
printVert (Related (More m r h)) =
  printVert (Related m)
  <> (if r then " " else " > ")
  <> printHoriz h

-- A disjunction of many selectors
type SomeSelectors = Array ASelector

-- Identity selector
matchAll :: ASelector
matchAll =
  { element: Nothing
  , classes: mempty
  , pseudoCls: mempty
  , pseudoEl: Nothing
  , attrs: mempty
  }

matchElement :: String -> ASelector
matchElement = matchElement' false
matchClass :: String -> ASelector
matchClass = matchClass' false
matchPseudoCls :: String -> ASelector
matchPseudoCls = matchPseudoCls' false
matchPseudoEl :: String -> ASelector
matchPseudoEl = matchPseudoEl' false
matchAttr :: AttrMatch -> ASelector
matchAttr = matchAttr' false

matchElement' :: Boolean -> String -> ASelector
matchElement' inverted name = matchAll
  { element = Just { inverted, name } }

matchClass' :: Boolean -> String -> ASelector
matchClass' inverted name = matchAll
  { classes = singleton name inverted }

matchPseudoCls' :: Boolean -> String -> ASelector
matchPseudoCls' inverted name = matchAll
  { pseudoCls = singleton name inverted }

matchPseudoEl' :: Boolean -> String -> ASelector
matchPseudoEl' inverted name = matchAll
  { pseudoEl = Just { inverted, name } }

matchAttr' :: Boolean -> AttrMatch -> ASelector
matchAttr' inverted match = matchAll
  { attrs = singleton match inverted }

selectToMatch :: Select -> ASelector
selectToMatch = selectToMatch' <<< (Tuple <@> false)

selectToMatch' :: Tuple Select Boolean -> ASelector
selectToMatch' (Tuple v i) = case v of
  Element s -> matchElement' i s
  Class s -> matchClass' i s
  PseudoCls s -> matchPseudoCls' i s
  PseudoEl s -> matchPseudoEl' i s
  Attribute s -> matchAttr' i s


-- div.container .item && div.other .item
-- div.container.other .item || div.container div.other .item || div.other div.container .item

-- .a ~ .c && .b ~ .d
-- .a.b ~ .c.d || .a ~ .b ~ .c.d || .b ~ .a ~ .c.d

-- .a .c && .b > .c
-- .a.b > .c || .a .b > .c

-- .a (>) .c && .b (+~) .c -- sym
-- .a (>) .b (+~) .c

-- (div && .container || *:hover) > (h1 && .selected)
-- ((div && .container) > h1 || (*:hover) > h1) && .selected
-- ((div && .container) > h1) && .selected || ((*:hover) > h1) && .selected
-- ((div && .container) > (h1 && .selected)) || ((*:hover) > (h1 && .selected))

-- .a ~ .b > .c .d ~ .e + .f > .g && .h > .i ~ .j ~.k .l + .m .n

-- a ~ b + c + d ~ e + f && g ~ h + i ~ j + k

{-
combineRelations :: Selectree -> Selectree -> Array Selectree
combineRelations (One s1) (One s2) = One <$> conjoin s1 s2
combineRelations (One s1) (Related more rel s2) =
  Related more rel <$> conjoin s1 s2
combineRelations (Related more rel s1) (One s2) =
  Related more rel <$> conjoin s1 s2
combineRelations (Related m1 r1 s1) (Related m2 r2 s2) =
  let
    p1 = un Rel $ view rel r1
    p2 = un Rel $ view rel r2
  in case p1, p2 of
    { vertical: true }, { vertical: false } ->
      combineDisp m1 p1.immediate s1 m2 p2.immediate s2
    { vertical: false }, { vertical: true } ->
      combineDisp m2 p2.immediate s2 m1 p1.immediate s1
    { immediate: true }, { immediate: true } ->
      combineDirect p1.vertical m1 m2 s1 s2
    { immediate: false }, { immediate: false } ->
      combinePerm3 p1.vertical m1 m2 s1 s2
    { immediate: false }, { immediate: true } ->
      combinePerm2 p1.vertical m1 m2 s1 s2
    { immediate: true }, { immediate: false } ->
      combinePerm2 p1.vertical m2 m1 s2 s1

mkV = if _ then Child else Descendant
mkH = if _ then Next else Later
mkI = if _ then Child else Next
mkO = if _ then Descendant else Later

combineDisp m1 i1 s1 m2 i2 s2 = pure $
  Related (Related m1 (mkV i1) m2) (mkH i2) s2
combineDirect v m1 m2 s1 s2 =
  Related <$> combineRelations m1 m2 <@> mkI v <*> conjoin s1 s2
combinePerm3 v m1 m2 s1 s2 =
  let cnjnd = conjoin s1 s2
  in  Related <$> combineRelations m1 m2 <@> mkO v <*> cnjnd
  <|> Related (Related m1 (mkO v) m2) (mkO v) <$> cnjnd
  <|> Related (Related m1 (mkO v) m2) (mkO v) <$> cnjnd
combinePerm2 v m1 m2 s1 s2 =
  let cnjnd = conjoin s1 s2
  in  Related <$> combineRelations m1 m2 <@> mkI v <*> cnjnd
  <|> Related (Related m1 (mkO v) m2) <$> cnjnd
  <|> Related (Related m1 (mkO v) m2) <$> cnjnd
-}

{-
combineRelations (Rel a) (Rel b) =
  let
    combineDisp
    combineDirect
    combinePerm3
    combinePerm2
  in case a, b of
    { vertical: true }, { vertical: false } ->
      combineDisp a.immediate b.immediate
    { vertical: false }, { vertical: true } ->
      combineDisp b.immediate a.immediate
    { immediate: true }, { immediate: true } ->
      combineDirect a.vertical
    { immediate: false }, { immediate: false } ->
      combinePerm3 a.vertical
    { immediate: false }, { immediate: true } ->
      combinePerm2 a.vertical a b
    { immediate: true }, { immediate: false } ->
      combinePerm2 a.vertical b a
-}

-- Prevent inconsistent values from appearing in the map
dedup :: forall k v. Ord k => Eq v => Map k v -> Map k v -> Maybe (Map k v)
dedup l r = sequence $ unionWith merger (l <#> Just) (r <#> Just)
  where
    merger :: Maybe v -> Maybe v -> Maybe v
    merger (Just a) (Just b) | a == b = Just a
    merger _ _ = Nothing

-- Conjoin two selectors, returning `Nothing` if the result is provably `false`
-- (e.g. if it would have to match two different element types or pseudo-element
-- types at once).
conjoin :: forall f. Alternative f => ASelector -> ASelector -> f ASelector
conjoin a b = oneOfMap pure $ lift5
  { element: _, attrs: _, classes: _, pseudoCls: _, pseudoEl: _ }
  (combE a.element b.element)
  (dedup a.attrs b.attrs)
  (dedup a.classes b.classes)
  (dedup a.pseudoCls b.pseudoCls)
  (combE a.pseudoEl b.pseudoEl)
  where
    combE Nothing v = Just v
    combE v Nothing = Just v
    combE l@(Just a) r@(Just b) =
      case a.inverted, b.inverted of
        false, true -> Just l
        true, false -> Just r
        _, _ | a.name == b.name -> Just l
             | otherwise -> Nothing

-- Conjoin many selectors
conjoinFold :: SomeSelectors -> Maybe ASelector
conjoinFold = foldl (flip (foldM conjoin)) (Just matchAll)

fromNF :: NormalForm Select -> SomeSelectors
fromNF = unwrap >>> toArrays >>> mapMaybe
  (map selectToMatch' >>> conjoinFold)

ensure :: String -> String -> String
ensure s "" = s
ensure _ s = s

-- An empty string means false, which we represent with :not(*)
print :: SomeSelectors -> String
print = ensure ":not(*)" <<< joinWith ", " <<< map print1

print1 :: ASelector -> String
print1 v = ensure "*" $ e <> as <> c <> pc <> pe where
  invert false n = n
  invert true n = ":not(" <> n <> ")"
  -- Print the element, or *
  e = case v.element of
    Nothing -> ""
    Just { inverted, name } ->
      invert inverted name
  -- Print attributes in brackets[]
  as = v.attrs # foldMapWithIndex \(AttrMatch { attr, match }) i ->
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
  c = v.classes # foldMapWithIndex \name i ->
    invert i ("." <> name)
  -- Print pseudo-classes, preceded by colons:
  pc = v.pseudoCls # foldMapWithIndex \name i ->
    invert i (":" <> name)
  -- Print the pseudo-element (if applicable), preceded by a double colon::
  pe = v.pseudoEl # foldMap \{ inverted, name } ->
    invert inverted ("::" <> name)

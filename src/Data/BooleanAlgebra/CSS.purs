module Data.BooleanAlgebra.CSS where

import Prelude

import Control.Apply (lift5)
import Data.Array (mapMaybe)
import Data.BooleanAlgebra.NormalForm (NormalForm, toArrays, free)
import Data.Foldable (all, foldM, foldMap, foldl)
import Data.FoldableWithIndex (foldMapWithIndex)
import Data.HeytingAlgebra (ff, tt)
import Data.Map (Map, singleton, unionWith)
import Data.Maybe (Maybe(..))
import Data.Monoid (mempty)
import Data.Newtype (class Newtype, un, unwrap)
import Data.String (joinWith)
import Data.Traversable (sequence)
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
conjoin :: ASelector -> ASelector -> Maybe ASelector
conjoin a b = lift5
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

print :: SomeSelectors -> String
print = ensure <<< joinWith ", " <<< map print1 where
  -- An empty string means false, which we represent with :not(*)
  ensure "" = ":not(*)"
  ensure s = s
  invert false n = n
  invert true n = ":not(" <> n <> ")"
  print1 :: ASelector -> String
  print1 v = e <> as <> c <> pc <> pe where
    -- Print the element, or *
    e = case v.element of
      Nothing -> "*"
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

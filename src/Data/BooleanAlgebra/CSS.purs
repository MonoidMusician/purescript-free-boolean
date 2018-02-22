module Data.BooleanAlgebra.CSS where

import Prelude

import Control.Apply (lift2, lift5)
import Control.MonadZero (class MonadZero)
import Control.Plus (class Plus, empty, (<|>))
import Data.BooleanAlgebra.Free (Free(..), free, simplify)
import Data.Foldable (all, foldMap, foldl, oneOfMap)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex)
import Data.HeytingAlgebra (ff, tt)
import Data.Map (Map, singleton, unionWith)
import Data.Maybe (Maybe(..))
import Data.Monoid (mempty)
import Data.Monoid.Alternate (Alternate(..))
import Data.Newtype (class Newtype, un)
import Data.String (joinWith)
import Data.Traversable (sequence)

data Select
  = Element String
  | Class String
  | PseudoCls String
  | PseudoEl String
  | Attribute AttrMatch

derive instance eqSelect :: Eq Select
derive instance ordSelect :: Ord Select

newtype AttrMatch = AttrMatch
  { attr :: String
  , match :: Maybe MatchValue
  }

derive instance eqAttrMatch :: Eq AttrMatch
derive instance ordAttrMatch :: Ord AttrMatch

newtype MatchValue = MatchValue
  { matchType :: MatchValueType
  , value :: String
  , insensitive :: Boolean
  }

derive instance eqMatchValue :: Eq MatchValue
derive instance ordMatchValue :: Ord MatchValue

data MatchValueType
  = Exact -- [attr=value]
  | ListContains -- [attr~=value]
  | Contains -- [attr*=value]
  | StartsWith -- [attr^=value]
  | EndsWith -- [attr$=value]
  | LangCode -- [attr|=value]

derive instance eqMatchValueType :: Eq MatchValueType
derive instance ordMatchValueType :: Ord MatchValueType

newtype Selector = S (Free Select)
derive instance newtypeSelector :: Newtype Selector _
derive newtype instance heytingAlgebraSelector :: HeytingAlgebra Selector
derive newtype instance booleanAlgebraSelector :: BooleanAlgebra Selector
instance showSelector :: Show Selector where
  show = un S >>> simplify >>> normalize >>> print

element :: String -> Selector
element = S <<< free <<< Element

classes :: Array String -> Selector
classes = all (S <<< free <<< Class)

pseudo :: String -> Selector
pseudo = S <<< free <<< PseudoCls

pseudoElement :: String -> Selector
pseudoElement = S <<< free <<< PseudoEl

anything :: Selector
anything = tt

nothing :: Selector
nothing = ff

div :: Selector
div = element "div"

hover :: Selector
hover = pseudo "hover"

before :: Selector -> Selector
before = conj $ pseudoElement "before"

after :: Selector -> Selector
after = conj $ pseudoElement "after"

attrExists :: String -> Selector
attrExists attr = S $ free $ Attribute $ AttrMatch
  { attr, match: Nothing }

exactAttr :: String -> String -> Selector
exactAttr a v = attrValue a $ MatchValue
  { matchType: Exact
  , value: v
  , insensitive: false
  }

attrValue :: String -> MatchValue -> Selector
attrValue a v = S $ free $ Attribute $ AttrMatch { attr: a, match: Just v }

type AThing =
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

type Items = Map String Boolean

matchAll :: AThing
matchAll =
  { element: Nothing
  , classes: mempty
  , pseudoCls: mempty
  , pseudoEl: Nothing
  , attrs: mempty
  }

matchElement :: String -> AThing
matchElement = matchElement' false
matchClass :: String -> AThing
matchClass = matchClass' false
matchPseudoCls :: String -> AThing
matchPseudoCls = matchPseudoCls' false
matchPseudoEl :: String -> AThing
matchPseudoEl = matchPseudoEl' false
matchAttr :: AttrMatch -> AThing
matchAttr = matchAttr' false

matchElement' :: Boolean -> String -> AThing
matchElement' inverted name = matchAll
  { element = Just { inverted, name } }

matchClass' :: Boolean -> String -> AThing
matchClass' inverted name = matchAll
  { classes = singleton name inverted }

matchPseudoCls' :: Boolean -> String -> AThing
matchPseudoCls' inverted name = matchAll
  { pseudoCls = singleton name inverted }

matchPseudoEl' :: Boolean -> String -> AThing
matchPseudoEl' inverted name = matchAll
  { pseudoEl = Just { inverted, name } }

matchAttr' :: Boolean -> AttrMatch -> AThing
matchAttr' inverted match = matchAll
  { attrs = singleton match inverted }

-- oneOfMapWithIndex ::
oneOfMapWithIndex ::
  forall f i a g b.
    FoldableWithIndex f i =>
    Plus g =>
  (f -> a -> g b) -> i a -> g b
oneOfMapWithIndex f = un Alternate <<< foldMapWithIndex (compose Alternate <<< f)

dedup :: forall k v. Ord k => Eq v => Map k v -> Map k v -> Maybe (Map k v)
dedup l r = sequence $ unionWith merger (l <#> Just) (r <#> Just)
  where
    merger :: Maybe v -> Maybe v -> Maybe v
    merger (Just a) (Just b) | a == b = Just a
    merger _ _ = Nothing

combine :: AThing -> AThing -> Maybe AThing
combine a b = lift5
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

combineAll :: forall f. MonadZero f => f AThing -> f AThing -> f AThing
combineAll a b = lift2 combine a b >>= oneOfMap pure

invert :: Array AThing -> Array AThing
invert = foldl combineAll (pure matchAll) <<< map invert1
  where
    invertElement { inverted, name } = pure $
      matchElement' (not inverted) name
    invertAttr match inverted = pure $
      matchAttr' (not inverted) match
    invertClass name inverted = pure $
      matchClass' (not inverted) name
    invertPseudoCls name inverted = pure $
      matchPseudoCls' (not inverted) name
    invertPseudoEl { inverted, name } = pure $
      matchPseudoEl' (not inverted) name
    invert1 :: AThing -> Array AThing
    invert1 a =
      oneOfMap invertElement a.element
      <|> oneOfMapWithIndex invertAttr a.attrs
      <|> oneOfMapWithIndex invertClass a.classes
      <|> oneOfMapWithIndex invertPseudoCls a.pseudoCls
      <|> oneOfMap invertPseudoEl a.pseudoEl

-- Disjunctive normal form
normalize :: Free Select -> Array AThing
normalize True = pure matchAll
normalize (Id a) = case a of
  Element s -> pure $ matchElement s
  Class s -> pure $ matchClass s
  PseudoCls s -> pure $ matchPseudoCls s
  PseudoEl s -> pure $ matchPseudoEl s
  Attribute s -> pure $ matchAttr s
normalize (Not a) = case a of
  Not b -> normalize b
  True -> empty
  _ -> invert (normalize a)
normalize (Or a b) = normalize a <|> normalize b
normalize (And a b) = normalize a `combineAll` normalize b

print :: Array AThing -> String
print = ensure <<< joinWith ", " <<< map print1 where
  -- An empty string means false, which we represent with :not(*)
  ensure "" = ":not(*)"
  ensure s = s
  invert false n = n
  invert true n = ":not(" <> n <> ")"
  print1 :: AThing -> String
  print1 v = e <> as <> c <> pc <> pe where
    e = case v.element of
      Nothing -> "*"
      Just { inverted, name } ->
        invert inverted name
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
    c = v.classes # foldMapWithIndex \name i ->
      invert i ("." <> name)
    pc = v.pseudoCls # foldMapWithIndex \name i ->
      invert i (":" <> name)
    pe = v.pseudoEl # foldMap \{ inverted, name } ->
      invert inverted ("::" <> name)

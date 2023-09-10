module Data.BooleanAlgebra.NormalForm where

import Prelude

import Control.Bind (bindFlipped)
import Data.Foldable (all, any, oneOfMap) as TF
import Data.Function (on)
import Data.HeytingAlgebra (ff, tt)
import Data.Lens (Iso', iso)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Map as M
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, over2, un)
import Data.Set as S
import Data.String (joinWith)
import Data.Traversable (sequence, traverse) as TF
import Data.Tuple (Tuple(..))

newtype NormalForm a = NF (AsSetMap a)
derive instance newtypeNormalForm :: Newtype (NormalForm a) _

instance eqNF :: Ord a => Eq (NormalForm a) where
  eq = eq `on` (un NF <<< normalize)

instance ordNF :: Ord a => Ord (NormalForm a) where
  compare = comparing (un NF <<< normalize)

instance showNF :: (Show a, Ord a) => Show (NormalForm a) where
  show a | a == tt = "tt"
  show a | a == ff = "ff"
  show a = a # normalize >>> un NF >>> toArrays >>>
    map (joinWith " && " <<< map shown) >>> joinWith " || " >>> wrapped where
      shown (Tuple a false) = "free " <> show a
      shown (Tuple a true) = "not free " <> show a
      wrapped a = "(" <> a <> ")"

type AsSetMap a = S.Set (M.Map a Boolean)
type AsArrays a = Array (Array (Tuple a Boolean))

asArray = identity :: Array ~> Array

toArrays :: forall a. Ord a => AsSetMap a -> AsArrays a
toArrays = S.toUnfoldable >>> map M.toUnfoldable

fromArrays :: forall a. Ord a => AsArrays a -> AsSetMap a
fromArrays = bindFlipped (TF.oneOfMap pure <<< inner) >>> S.fromFoldable where
  inner :: Array (Tuple a Boolean) -> Maybe (M.Map a Boolean)
  inner = TF.sequence <<< M.fromFoldableWith agreement <<< map (map Just)
  agreement (Just true) (Just true) = Just true
  agreement (Just false) (Just false) = Just false
  agreement _ _ = Nothing

overArrays :: forall a. Ord a => Iso' (AsSetMap a) (AsArrays a)
overArrays = iso toArrays fromArrays

free :: forall a. Ord a => a -> NormalForm a
free = NF <<< S.singleton <<< flip M.singleton false

liftFree :: forall a b. Ord a => BooleanAlgebra b => (a -> b) -> NormalForm a -> b
liftFree f (NF nf) = TF.any (TF.all f') (toArrays nf) where
  f' (Tuple v false) = f v
  f' (Tuple v true) = not f v

lowerFree :: forall a b. Ord a => BooleanAlgebra b => (NormalForm a -> b) -> a -> b
lowerFree f a = f (free a)

normalize :: forall a. Ord a => NormalForm a -> NormalForm a
normalize = not not

instance nfHeytingAlgebra :: Ord a => HeytingAlgebra (NormalForm a) where
  tt = NF (S.singleton M.empty)
  ff = NF S.empty
  not = _Newtype $ overArrays deMorgan where
    -- sequence distributes conjunctions and disjunctions over each other
    -- while map (map (map not)) actually negates the terms
    deMorgan = TF.traverse (map (map not))
  -- in disjunctive normal form, just need to append all the clauses together
  disj = over2 NF append
  -- could be optimized, but go through `||` instead
  conj m1 m2 = not (not m1 || not m2)
  implies a b = not a || b

instance nfBooleanAlgebra :: Ord a => BooleanAlgebra (NormalForm a)

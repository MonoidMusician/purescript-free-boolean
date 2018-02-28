module Data.InterTsil where

import Data.Bifunctor (class Bifunctor, bimap, rmap)
import Data.Bitraversable (class Bifoldable, class Bitraversable, bifoldMap, bifoldl, bifoldlDefault, bifoldr, bifoldrDefault, bisequenceDefault, bitraverse)
import Data.Either (Either(..))
import Data.Lens (Lens', lens')
import Data.Monoid (mempty)
import Data.Semigroup.Foldable (class Foldable1, fold1Default, foldMap1)
import Data.Semigroup.Traversable (class Traversable1, sequence1Default, traverse1)
import Data.Traversable (class Foldable, class Traversable)
import Data.Tuple (Tuple(..))
import Prelude (class Eq, class Functor, class Ord, flip, id, pure, (<$>), (<*>), (<>), (<@>))

data InterTsil a b = One b | More (InterTsil a b) a b
derive instance eqInterTsil :: (Eq a, Eq b) => Eq (InterTsil a b)
derive instance ordInterTsil :: (Ord a, Ord b) => Ord (InterTsil a b)

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

_last :: forall a b. Lens' (InterTsil a b) b
_last = lens' case _ of
  One s -> Tuple s \s' -> One s'
  More m a s -> Tuple s \s' -> More m a s'

concat :: forall a b. InterTsil a b -> a -> InterTsil a b -> InterTsil a b
concat m r (One s) = More m r s
concat m r (More m1 r1 s) = More (concat m r m1) r1 s

dimensionalize :: forall a b c d.
  (a -> Either b c) -> InterTsil a d ->
  InterTsil b (InterTsil c d)
dimensionalize f (One d) = One (One d)
dimensionalize f (More m a d) = case f a of
  Left b -> More (dimensionalize f m) b (One d)
  Right c -> _last (\m' -> More m' c d) (dimensionalize f m)

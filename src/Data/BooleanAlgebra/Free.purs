module Data.BooleanAlgebra.Free where

import Prelude

import Data.BooleanAlgebra (tt, ff)

data Free a
  = True
  | Id a
  | Or (Free a) (Free a)
  | And (Free a) (Free a)
  | Not (Free a)

instance freeBooleanHeytingAlgebra :: HeytingAlgebra (Free a) where
  tt = True
  ff = Not True
  not = Not
  disj = Or
  conj = And
  implies a b = Or (Not a) b

instance freeBooleanAlgebra :: BooleanAlgebra (Free a)

free :: forall a. a -> Free a
free = Id

liftFree :: forall a b. BooleanAlgebra b => (a -> b) -> Free a -> b
liftFree f (Id a) = f a
liftFree f (Not a) = not (liftFree f a)
liftFree f (And a b) = liftFree f a && liftFree f b
liftFree f (Or a b) = liftFree f a || liftFree f b
liftFree _ True = tt

lowerFree :: forall a b. BooleanAlgebra b => (Free a -> b) -> a -> b
lowerFree f a = f (Id a)

dm :: Free ~> Free
dm True = ff
dm (Not a) = a
dm (Or a b) = dm a && dm b
dm (And a b) = dm a || dm b
dm (Id a) = Not (Id a)

-- TODO: simplify with Ord to catch other tautologies and contradictions
simplify :: Free ~> Free
simplify True = tt
simplify (Not a) = dm (simplify a)
simplify (Or a b) = case simplify a, simplify b of
  True, _ -> tt
  _, True -> tt
  Not True, Not True -> ff
  x, y -> x || y
simplify (And a b) = case simplify a, simplify b of
  Not True, _ -> ff
  _, Not True -> ff
  True, True -> tt
  x, y -> x && y
simplify (Id a) = Id a

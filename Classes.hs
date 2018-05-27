{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Classes where

import Data.Constraint

class Category cat o | cat -> o where
  id' :: o a => cat a a
  (>>>) :: cat a b -> cat b c -> cat a c

(<<<) :: Category cat o => cat b c -> cat a b -> cat a c
f <<< g = g >>> f

class Distr2 o p | p -> o where distr2 :: (o a, o b) :- o (a `p` b)
class (Category cat o, Distr2 o p) => Bifunctor cat o p | p -> cat where
  bimap :: cat a b -> cat x y -> (a `p` x) `cat` (b `p` y)

lmap :: (Bifunctor cat o p, o x) =>
  a `cat` b -> (a `p` x) `cat` (b `p` x)
lmap l = bimap l id'

rmap :: (Bifunctor cat o p, o a) =>
  x `cat` y -> (a `p` x) `cat` (a `p` y)
rmap r = bimap id' r

class (Bifunctor cat o p, o i) => Monoidal cat o p i | p -> i, i -> p where
  assoc :: (o a, o b, o c) => ((a `p` b) `p` c) `cat` (a `p` (b `p` c))
  unassoc :: (o a, o b, o c) => (a `p` (b `p` c)) `cat` ((a `p` b) `p` c)

  lunit :: o x => (i `p` x) `cat` x
  unlunit :: o x => x `cat` (i `p` x)

  runit :: o x => (x `p` i) `cat` x
  unrunit :: o x => x `cat` (x `p` i)

class Monoidal cat o p i => Braided cat o p i where
  braid :: (o a, o b) => (a `p` b) `cat` (b `p` a)
  unbraid :: (o a, o b) => (b `p` a) `cat` (a `p` b)

class Braided cat o p i => Symmetric cat o p i

class Distr1 o d | d -> o where distr1 :: o a :- o (d a)
class (Symmetric cat o p i, Distr1 o d) =>
    CompactClosed cat o p i d | d -> p, p -> d where
  ev :: o a => (d a `p` a) `cat` i
  coev :: o a => i `cat` (a `p` d a)


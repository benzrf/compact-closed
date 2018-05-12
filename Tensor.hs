{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
module Tensor where

import Linear.V
import Linear.Matrix
import Linear.Vector
import GHC.TypeLits
import Data.Proxy

class Category cat k | cat -> k where
  id' :: k a => cat a a
  (>>>) :: (k a, k b, k c) => cat a b -> cat b c -> cat a c

class Category cat k => Bifunctor cat k p | p -> cat where
  bimap :: (k a, k b, k x, k y) =>
             cat a b -> cat x y -> (a `p` x) `cat` (b `p` y)

lmap :: (Bifunctor cat k p, k a, k b, k x) =>
  a `cat` b -> (a `p` x) `cat` (b `p` x)
lmap l = bimap l id'

rmap :: (Bifunctor cat k p, k a, k x, k y) =>
  x `cat` y -> (a `p` x) `cat` (a `p` y)
rmap r = bimap id' r

class (Bifunctor cat k p, k i) => Monoidal cat k p i | p -> i, i -> p where
  assoc :: (k a, k b, k c) => ((a `p` b) `p` c) `cat` (a `p` (b `p` c))
  unassoc :: (k a, k b, k c) => (a `p` (b `p` c)) `cat` ((a `p` b) `p` c)

  lunit :: k x => (i `p` x) `cat` x
  unlunit :: k x => x `cat` (i `p` x)

  runit :: k x => (x `p` i) `cat` x
  unrunit :: k x => x `cat` (x `p` i)

class Monoidal cat k p i => Braided cat k p i where
  braid :: (k a, k b) => (a `p` b) `cat` (b `p` a)
  unbraid :: (k a, k b) => (b `p` a) `cat` (a `p` b)

class Braided cat k p i => Symmetric cat k p i

class Symmetric cat k p i => CompactClosed cat p k i d | d -> p, p -> d where
  ev :: k a => (d a `p` a) `cat` i
  coev :: k a => i `cat` (a `p` d a)

-- a `cat` b ===> d a `p` b

data FinSpace = Free Nat | TensorSpace FinSpace FinSpace

instance Dim n => Dim (Free n) where
  reflectDim _ = reflectDim (Proxy :: Proxy n)
instance (Dim v, Dim w) => Dim (TensorSpace v w) where
  reflectDim _ = reflectDim (Proxy :: Proxy v) * reflectDim (Proxy :: Proxy w)

squash :: (Dim v, Dim w) => V v (V w k) -> V (TensorSpace v w) k
squash m = case fromVector (toVector m >>= toVector) of
  Just m' -> m'
  Nothing -> error "impossible?!"

otimes :: (Dim v, Dim w, Num k) => V v k -> V w k -> V (TensorSpace v w) k
otimes v w = squash (outer v w)

type K = Double
data FinVect :: FinSpace -> FinSpace -> * where
  FinVect :: V v (V w K) -> FinVect w v

deriving instance Show (FinVect v w)

instance Category FinVect Dim where
  id' = FinVect identity
  FinVect f >>> FinVect g = FinVect (g !*! f)

instance Bifunctor FinVect Dim TensorSpace where
  -- bimap :: cat a b -> cat x y -> (a `p` x) `cat` (b `p` y)
  bimap (FinVect f) (FinVect g) = FinVect r
    where r = outer (squash f) (squash g)

{-
class Bifunctor' cat p => Monoidal cat p i | p -> i, i -> p where
  assoc :: ((a `p` b) `p` c) `cat` (a `p` (b `p` c))
  unassoc :: (a `p` (b `p` c)) `cat` ((a `p` b) `p` c)

  lunit :: (i `p` x) `cat` x
  unlunit :: x `cat` (i `p` x)

  runit :: (x `p` i) `cat` x
  unrunit :: x `cat` (x `p` i)

class Monoidal cat p i => Braided cat p i where
  braid :: (a `p` b) `cat` (b `p` a)
  unbraid :: (b `p` a) `cat` (a `p` b)

class Braided cat p i => Symmetric cat p i

class Symmetric cat p i => CompactClosed cat p i d | d -> p, p -> d where
  ev :: (d a `p` a) `cat` i
  coev :: i `cat` (a `p` d a)



toDoubleDual :: CompactClosed cat p i d =>
  a `cat` d (d a)
toDoubleDual =
  unrunit >>> rmap coev >>> unassoc >>> lmap (braid >>> ev) >>> lunit

fromDoubleDual :: CompactClosed cat p i d =>
  d (d a) `cat` a
fromDoubleDual =
  runit <<< rmap (ev <<< braid) <<< assoc <<< lmap coev <<< unlunit

dualTensor :: CompactClosed cat p i d =>
  d (a `p` b) `cat` (d a `p` d b)
dualTensor =
  unrunit >>> rmap coev >>> unassoc >>> unrunit >>> rmap coev >>>
    unassoc >>> lmap (assoc >>> rmap braid >>> unassoc) >>> assoc >>>
    lmap (assoc >>> ev) >>> lunit

tensorDual :: CompactClosed cat p i d =>
   (d a `p` d b) `cat` d (a `p` b)
tensorDual =
  runit <<< rmap (ev <<< braid) <<< assoc <<< runit <<< rmap (ev <<< braid) <<<
    assoc <<< lmap (unassoc <<< rmap braid <<< assoc) <<< unassoc <<<
    lmap (unassoc <<< braid <<< coev) <<< unlunit
-}


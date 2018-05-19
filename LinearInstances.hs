{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
module LinearInstances where

import Classes
import Linear.V
import Linear.Matrix
import Linear.Vector
import GHC.TypeLits
import Data.Proxy
import Data.Kind
import Data.Vector
import Data.Constraint
import Control.Applicative

data FinSpace = Free Nat | TensorSpace FinSpace FinSpace | DualSpace FinSpace

instance Dim n => Dim (Free n) where
  reflectDim _ = reflectDim (Proxy :: Proxy n)
instance (Dim v, Dim w) => Dim (TensorSpace v w) where
  reflectDim _ = reflectDim (Proxy :: Proxy v) * reflectDim (Proxy @w)
instance Dim v => Dim (DualSpace v) where
  reflectDim _ = reflectDim (Proxy :: Proxy v)

{-
data FinSpaceEl v k where
  FreeEl :: V n k -> FinSpaceEl (Free n) k
  TensorSpaceEl :: FinSpaceEl v (FinSpaceEl w k) ->
    FinSpaceEl (TensorSpace v w) k
  DualSpaceEl :: FinSpaceEl v k -> FinSpaceEl (DualSpace v) l

instance Functor (FinSpaceEl v) where

deriving instance Traversable (FinSpaceEl v)
-}

-- For j-dimensional 'v' and k-dimensional 'w', 'v otimes w' is
-- (j * k)-dimensional.
-- For 'm :: V (v otimes w) k', the coefficient for v_n otimes w_m is at index
-- [n, m] = n * k + m.

badFromVector :: Dim n => Vector a -> V n a
badFromVector v = case fromVector v of
  Just v' -> v'
  Nothing -> error "impossible?!"

squash :: (Dim v, Dim w) => V v (V w k) -> V (TensorSpace v w) k
squash m = badFromVector $ toVector m >>= toVector

unsquash ::
  forall v w k. (Dim v, Dim w) => V (TensorSpace v w) k -> V v (V w k)
unsquash (V m) = badFromVector $ generate vDim row
  where vDim = reflectDim (Proxy @v)
        wDim = reflectDim (Proxy @w)
        row i = badFromVector $ slice (i * wDim) wDim m

otimes :: (Dim v, Dim w, Num k) => V v k -> V w k -> V (TensorSpace v w) k
otimes v w = squash (outer v w)

type K = Double
data FinVect :: FinSpace -> FinSpace -> Type where
  FinVect :: (Dim v, Dim w) => V w (V v K) -> FinVect v w

deriving instance (Dim v, Dim w) => Show (FinVect v w)

instance Category FinVect Dim where
  id' = FinVect identity
  FinVect f >>> FinVect g = FinVect (g !*! f)

instance Distr2 Dim TensorSpace where distr2 = Sub Dict
instance Bifunctor FinVect Dim TensorSpace where
  -- this might be refactorable
  bimap (FinVect (V f)) (FinVect (V g)) =
    FinVect . badFromVector $ liftA2 otimes f g

-- unsafe(-ish)!!
badLinIso :: (Dim v, Dim w) => FinVect v w
badLinIso = FinVect . badFromVector . toVector $ identity

transposeV :: Dim v => FinVect v (DualSpace v)
transposeV = badLinIso

untransposeV :: Dim v => FinVect (DualSpace v) v
untransposeV = badLinIso

instance Monoidal FinVect Dim TensorSpace (Free 1) where
  assoc = badLinIso
  unassoc = badLinIso

  lunit = badLinIso
  unlunit = badLinIso

  runit = badLinIso
  unrunit = badLinIso

instance Braided FinVect Dim TensorSpace (Free 1) where
  -- TODO this is wrong!!
  braid = badLinIso
  unbraid = braid

instance Symmetric FinVect Dim TensorSpace (Free 1)

instance Distr1 Dim DualSpace where distr1 = Sub Dict
instance CompactClosed FinVect Dim TensorSpace (Free 1) DualSpace where
  -- this could probably stand to be nicer.
  ev = lmap untransposeV >>> FinVect (pure . squash $ identity)
  coev = FinVect (fmap pure . squash $ identity) >>> rmap transposeV


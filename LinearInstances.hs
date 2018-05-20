{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
module LinearInstances where

import Classes
import Linear.V
import Linear.V1
import Linear.Matrix
import Linear.Vector
import GHC.TypeLits
import Data.Proxy
import Data.Kind
import Data.Vector
import Data.Kind
import Data.Typeable
import Data.Constraint
import Control.Applicative
import Data.Functor.Bind
import Data.Distributive
import Control.Monad
import IPPrint

badFromVector :: Dim n => Vector a -> V n a
badFromVector v = case fromVector v of
  Just v' -> v'
  Nothing -> error "impossible?!"

data FinSpace = Free Nat | TensorSpace FinSpace FinSpace | DualSpace FinSpace
data FinSpaceV v where
  FreeV :: KnownNat n => FinSpaceV (Free n)
  TensorSpaceV :: FinSpaceV v -> FinSpaceV w -> FinSpaceV (v `TensorSpace` w)
  DualSpaceV :: FinSpaceV v -> FinSpaceV (DualSpace v)

fsDim :: FinSpaceV v -> Int
fsDim fsv@FreeV = fromInteger (natVal (mkProx fsv))
  where mkProx :: FinSpaceV (Free n) -> Proxy n
        mkProx _ = Proxy
fsDim (TensorSpaceV v w) = fsDim v * fsDim w
fsDim (DualSpaceV v) = fsDim v

class KnownFS v where reflectFS :: proxy v -> FinSpaceV v
instance KnownNat n => KnownFS (Free n) where
  reflectFS _ = FreeV
instance (KnownFS v, KnownFS w) => KnownFS (TensorSpace v w) where
  reflectFS _ = TensorSpaceV (reflectFS @v Proxy) (reflectFS @w Proxy)
instance KnownFS v => KnownFS (DualSpace v) where
  reflectFS _ = DualSpaceV (reflectFS @v Proxy)

{-
instance KnownFS v => Dim v where
  reflectDim _ = fsDim (reflectFS @v Proxy)
-}

data FinEl v a where
  FreeEl :: V n a -> FinEl (Free n) a
  TensorSpaceEl :: FinEl w (FinEl v a) ->
    FinEl (TensorSpace v w) a
  DualSpaceEl :: FinEl v a -> FinEl (DualSpace v) a

deriving instance Show a => Show (FinEl v a)
deriving instance Eq a => Eq (FinEl v a)

getFreeEl :: FinEl (Free n) a -> V n a
getFreeEl (FreeEl vec) = vec

getTensorSpaceEl :: FinEl (TensorSpace v w) a -> FinEl w (FinEl v a)
getTensorSpaceEl (TensorSpaceEl m) = m

getDualSpaceEl :: FinEl (DualSpace v) a -> FinEl v a
getDualSpaceEl (DualSpaceEl d) = d

instance Functor (FinEl v) where
  fmap f (FreeEl vec) = FreeEl (fmap f vec)
  fmap f (TensorSpaceEl m) = TensorSpaceEl (fmap (fmap f) m)
  fmap f (DualSpaceEl d) = DualSpaceEl (fmap f d)

instance Apply (FinEl v) where
  FreeEl f <.> FreeEl x = FreeEl (f <.> x)
  TensorSpaceEl f <.> TensorSpaceEl x = TensorSpaceEl (liftF2 (<.>) f x)
  DualSpaceEl f <.> DualSpaceEl x = DualSpaceEl (f <.> x)

instance KnownFS v => Applicative (FinEl v) where
  pure = p (reflectFS @v Proxy)
    where p :: FinSpaceV v' -> a -> FinEl v' a
          p FreeV x = FreeEl (pure x)
          p (TensorSpaceV v w) x = TensorSpaceEl (p w (p v x))
          p (DualSpaceV v) x = DualSpaceEl (p v x)

  (<*>) = (<.>)

{-
instance Bind (FinEl v) where
  FreeEl vec >>- f =
    let f' a = case f a of FreeEl vec' -> vec'
    in  FreeEl (vec >>- f')
  TensorSpaceEl m >>- f = TensorSpaceEl . badFromVector . imap row $ m
    where row i = undefined
  DualSpaceEl d >>- f =
    let f' a = case f a of DualSpaceEl d' -> d'
    in  DualSpaceEl (d >>- f')

instance KnownFS v => Monad (FinEl v) where
  return = pure
  (>>=) = (>>-)
-}

instance Foldable (FinEl v) where
  foldMap f (FreeEl vec) = foldMap f vec
  foldMap f (TensorSpaceEl m) = foldMap (foldMap f) m
  foldMap f (DualSpaceEl d) = foldMap f d

instance Traversable (FinEl v) where
  sequenceA (FreeEl vec) = FreeEl <$> sequenceA vec
  sequenceA (TensorSpaceEl m) =
    fmap TensorSpaceEl . sequenceA . fmap sequenceA $ m
  sequenceA (DualSpaceEl d) = DualSpaceEl <$> sequenceA d

instance KnownFS v => Distributive (FinEl v) where
  distribute = go (reflectFS @v Proxy)
    where go :: Functor f =>
            FinSpaceV v' -> f (FinEl v' a) -> FinEl v' (f a)
          go FreeV = FreeEl . distribute . fmap getFreeEl
          go (TensorSpaceV v w) = TensorSpaceEl . fmap (go v) . go w .
            fmap getTensorSpaceEl
          go (DualSpaceV v) = DualSpaceEl . go v .  fmap getDualSpaceEl

instance KnownFS v => Additive (FinEl v) where
  zero = pure 0

free :: KnownNat n => V n a -> FinEl (Free n) a
free = FreeEl . badFromVector . toVector

{-
squash :: (KnownFS v, KnownFS w) => V v (V w k) -> V (TensorSpace v w) k
squash m = badFromVector $ toVector m >>= toVector

unsquash ::
  forall v w k. (KnownFS v, KnownFS w) => V (TensorSpace v w) k -> V v (V w k)
unsquash (V m) = badFromVector $ generate vDim row
  where vDim = reflectDim (Proxy @v)
        wDim = reflectDim (Proxy @w)
        row i = badFromVector $ slice (i * wDim) wDim m
-}

otimes :: (KnownFS v, KnownFS w, Num k) =>
  FinEl v k -> FinEl w k -> FinEl (TensorSpace v w) k
otimes v w = TensorSpaceEl (outer w v)

type K = Double
data FinVect :: FinSpace -> FinSpace -> Type where
  FinVect :: (KnownFS v, KnownFS w) => FinEl w (FinEl v K) -> FinVect v w
type EndoFV v = FinVect v v

deriving instance Eq (FinVect v w)
deriving instance Show (FinVect v w)

getFinVect :: FinVect v w -> ((KnownFS v, KnownFS w) => FinEl w (FinEl v K))
getFinVect (FinVect m) = m

infixr 0 $*
($*) :: FinVect v w -> FinEl v K -> FinEl w K
FinVect m $* v = m !* v

instance Category FinVect KnownFS where
  id' = FinVect identity
  FinVect f >>> FinVect g = FinVect (g !*! f)

instance Distr2 KnownFS TensorSpace where distr2 = Sub Dict
instance Bifunctor FinVect KnownFS TensorSpace where
  -- this might be refactorable
  -- m1 :: b (a K), m2 :: y (x K)
  -- we want: y (b (x (a K)))
  bimap (FinVect m1) (FinVect m2) = FinVect (TensorSpaceEl m)
    where m = fmap (\row2 -> fmap (\row1 -> row1 `otimes` row2) m1) m2

{-
-- unsafe(-ish)!!
badLinIso :: (KnownFS v, KnownFS w) => FinVect v w
badLinIso = FinVect . badFromVector . toVector $ identity

transposeV :: KnownFS v => FinVect v (DualSpace v)
transposeV = badLinIso

untransposeV :: KnownFS v => FinVect (DualSpace v) v
untransposeV = badLinIso
-}

instance Monoidal FinVect KnownFS TensorSpace (Free 1) where
  assoc = FinVect . TensorSpaceEl . TensorSpaceEl $ i
    where i = fmap getTensorSpaceEl . getTensorSpaceEl . getFinVect $ id'

  unassoc = FinVect . TensorSpaceEl . fmap TensorSpaceEl $ i
    where i = getTensorSpaceEl . getTensorSpaceEl . getFinVect $ id'

  lunit = FinVect . fmap (first . getFreeEl) $ i
    where first v = case fromV v of V1 x -> x
          i = getTensorSpaceEl . getFinVect $ id'
  unlunit = FinVect . TensorSpaceEl . fmap (FreeEl . pure) . getFinVect $ id'

  runit = FinVect . first . getFreeEl $ i
    where first v = case fromV v of V1 x -> x
          i = getTensorSpaceEl . getFinVect $ id'
  unrunit = FinVect . TensorSpaceEl . FreeEl . pure . getFinVect $ id'

instance Braided FinVect KnownFS TensorSpace (Free 1) where
  braid = FinVect . TensorSpaceEl . transpose $ i
    where i = getTensorSpaceEl . getFinVect $ id'
  unbraid = braid

instance Symmetric FinVect KnownFS TensorSpace (Free 1)

instance Distr1 KnownFS DualSpace where distr1 = Sub Dict
instance CompactClosed FinVect KnownFS TensorSpace (Free 1) DualSpace where
  ev = FinVect . FreeEl . pure . TensorSpaceEl . fmap DualSpaceEl $ identity
  coev = FinVect . fmap (FreeEl . pure) . TensorSpaceEl . DualSpaceEl $ identity


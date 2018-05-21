{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
module LinearInstancesSparse where

import Classes
import Linear.V1
import Linear.Matrix
import Linear.Vector
import GHC.TypeLits
import Data.Proxy
import Data.Kind
-- import Data.Vector
import Data.Kind
import Data.Maybe
import Data.Monoid
import Data.Typeable
import Data.Constraint
import Control.Applicative
import Data.Functor.Bind
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as M
import Data.Finite
import Data.Distributive
import Control.Monad
import IPPrint

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

data FSIx v where
  FreeIx :: Finite n -> FSIx (Free n)
  TensorSpaceIx :: FSIx v -> FSIx w -> FSIx (TensorSpace v w)
  DualSpaceIx :: FSIx v -> FSIx (DualSpace v)

deriving instance Show (FSIx v)
deriving instance Eq (FSIx v)

instance Ord (FSIx v) where
  compare (FreeIx n) (FreeIx m) = n `compare` m
  compare (TensorSpaceIx v_i w_i) (TensorSpaceIx v_j w_j) =
    compare v_i v_j <> compare w_i w_j
  compare (DualSpaceIx d_i) (DualSpaceIx d_j) = compare d_i d_j

instance KnownFS v => Enum (FSIx v) where
  toEnum = go (reflectFS @v Proxy)
    where go :: FinSpaceV v' -> Int -> FSIx v'
          go FreeV i = FreeIx (toEnum i)
          go (TensorSpaceV v w) i =
            let (q, r) = i `quotRem` fsDim w
            in  TensorSpaceIx (go v q) (go w r)
          go (DualSpaceV d) i = DualSpaceIx (go d i)

  fromEnum = go (reflectFS @v Proxy)
    where go :: FinSpaceV v' -> FSIx v' -> Int
          go FreeV (FreeIx i) = fromEnum i
          go (TensorSpaceV v w) (TensorSpaceIx v_i w_i) =
            go v v_i * fsDim w + go w w_i
          go (DualSpaceV d) (DualSpaceIx d_i) = go d d_i

-- hmmm... this technically doesn't work if we're 0-dimensional...
instance KnownFS v => Bounded (FSIx v) where
  minBound = toEnum 0
  maxBound = toEnum (fsDim (reflectFS @v Proxy) - 1)

enumerate :: (Enum a, Bounded a) => [a]
enumerate = [minBound..maxBound]

-- TODO is this in asc key order???
newtype FinEl v k = FinEl {getCoords :: Map (FSIx v) k}
  deriving (Functor, Foldable, Traversable, Eq)

finElSize :: FinEl v k -> Int
finElSize = length . getCoords

deriving instance (Show (FSIx v), Show k) => Show (FinEl v k)

deriving instance Apply (FinEl v)

instance KnownFS v => Applicative (FinEl v) where
  pure x = FinEl . M.fromAscList $ zip enumerate (repeat x)
  (<*>) = (<.>)

deriving instance Additive (FinEl v)

identity' :: (Num k, KnownFS v) => FinEl v (FinEl v k)
identity' = FinEl (M.fromAscList entries)
  where entries = map (\i -> (i, FinEl (M.singleton i 1))) enumerate
{-
identity' :: (Num k, KnownFS v) => FinEl (TensorSpace v v) k
identity' = FinEl (M.fromAscList entries)
  where entries = zip diag (repeat 1)
        diag = zipWith TensorSpaceIx all all
        all = [minBound..maxBound]
-}

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
instance KnownFS v => Distributive (FinEl v) where
  distribute = go (reflectFS @v Proxy)
    where go :: Functor f =>
            FinSpaceV v' -> f (FinEl v' a) -> FinEl v' (f a)
          go FreeV = FreeEl . distribute . fmap getFreeEl
          go (TensorSpaceV v w) = TensorSpaceEl . fmap (go v) . go w .
            fmap getTensorSpaceEl
          go (DualSpaceV v) = DualSpaceEl . go v .  fmap getDualSpaceEl
-}

free :: KnownNat n => [a] -> FinEl (Free n) a
free = FinEl . M.fromAscList . zip [minBound..]

otimes :: (KnownFS v, KnownFS w, Num k) =>
  FinEl v k -> FinEl w k -> FinEl (TensorSpace v w) k
otimes (FinEl v) (FinEl w) = FinEl . M.fromAscList $ do
  (i, x) <- M.toAscList v
  (j, y) <- M.toAscList w
  return (TensorSpaceIx i j, x * y)

type K = Double
data FinVect :: FinSpace -> FinSpace -> Type where
  FinVect :: (KnownFS v, KnownFS w) => FinEl w (FinEl v K) -> FinVect v w
type FVEndo v = FinVect v v

deriving instance Eq (FinVect v w)
deriving instance Show (FinVect v w)

getFinVect :: FinVect v w ->
  ((KnownFS v, KnownFS w) => FinEl w (FinEl v K))
getFinVect (FinVect m) = m

getFVCoords :: FinVect v w -> Map (FSIx w) (Map (FSIx v) K)
getFVCoords (FinVect (FinEl m)) = getCoords <$> m

fromFVCoords :: (KnownFS v, KnownFS w) => Map (FSIx w) (Map (FSIx v) K) ->
  FinVect v w
fromFVCoords = FinVect . FinEl . fmap FinEl

fvSize :: FinVect v w -> (Int, Int)
fvSize f = (length m, sum (length <$> m))
  where m = getFVCoords f

matrixOf :: FinVect v w -> [[K]]
matrixOf f@(FinVect _) = map (flip map enumerate . entry) enumerate
  where m = getFVCoords f
        entry i j = fromMaybe 0 $ M.lookup i m >>= M.lookup j

infixr 0 $*
($*) :: FinVect v w -> FinEl v K -> FinEl w K
FinVect m $* v = m !* v

instance Category FinVect KnownFS where
  -- not actually an identity of (>>>)
  -- TODO figure this out
  id' = FinVect identity'
  FinVect f >>> FinVect g = FinVect (g !*! f)

instance Distr2 KnownFS TensorSpace where distr2 = Sub Dict
instance Bifunctor FinVect KnownFS TensorSpace where
  -- this might be refactorable
  -- f :: b (a K), g :: y (x K)
  -- we want: (b, y) ((a, x) K)
  bimap (FinVect f) (FinVect g) = FinVect . FinEl . M.fromAscList $ do
    (i, fRow) <- M.toAscList . getCoords $ f
    (j, gRow) <- M.toAscList . getCoords $ g
    return (TensorSpaceIx i j, fRow `otimes` gRow)

-- TODO refactor this!!
instance Monoidal FinVect KnownFS TensorSpace (Free 1) where
  assoc = fromFVCoords . M.fromAscList $ do
    i <- enumerate
    j <- enumerate
    k <- enumerate
    let s = M.singleton (TensorSpaceIx (TensorSpaceIx i j) k) 1
    return (TensorSpaceIx i (TensorSpaceIx j k), s)

  unassoc = fromFVCoords . M.fromAscList $ do
    i <- enumerate
    j <- enumerate
    k <- enumerate
    let s = M.singleton (TensorSpaceIx i (TensorSpaceIx j k)) 1
    return (TensorSpaceIx (TensorSpaceIx i j) k, s)

  lunit = fromFVCoords . M.fromAscList $ do
    i <- enumerate
    return (i, M.singleton (TensorSpaceIx (FreeIx 0) i) 1)

  unlunit = fromFVCoords . M.fromAscList $ do
    i <- enumerate
    return (TensorSpaceIx (FreeIx 0) i, M.singleton i 1)

  runit = fromFVCoords . M.fromAscList $ do
    i <- enumerate
    return (i, M.singleton (TensorSpaceIx i (FreeIx 0)) 1)

  unrunit = fromFVCoords . M.fromAscList $ do
    i <- enumerate
    return (TensorSpaceIx i (FreeIx 0), M.singleton i 1)

instance Braided FinVect KnownFS TensorSpace (Free 1) where
  braid = fromFVCoords . M.fromAscList $ do
    i <- enumerate
    j <- enumerate
    return (TensorSpaceIx i j, M.singleton (TensorSpaceIx j i) 1)
  unbraid = braid

instance Symmetric FinVect KnownFS TensorSpace (Free 1)

instance Distr1 KnownFS DualSpace where distr1 = Sub Dict
instance CompactClosed FinVect KnownFS TensorSpace (Free 1) DualSpace where
  ev = fromFVCoords . M.singleton (FreeIx 0) . M.fromAscList $ do
    i <- enumerate
    return (TensorSpaceIx (DualSpaceIx i) i, 1)

  coev = fromFVCoords . M.fromAscList $ do
    i <- enumerate
    return (TensorSpaceIx i (DualSpaceIx i), M.singleton (FreeIx 0) 1)


{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeOperators #-}
module CompactClosed.Test where

import CompactClosed.AIN
import CompactClosed.Classes
import CompactClosed.LinearInstancesSparse

type GE w = FinVect (Free 1) w

ge :: KnownFS w => FinEl w K -> GE w
ge = FinVect . fmap (free . pure)

type Scalar = Free 1
type X = Free 3
type A = Free 2
type B = Free 2


s :: GE Scalar
s = ge $ free [3]

v :: GE (DualSpace X `TensorSpace` DualSpace B)
v = ge $ dual (free [1, 2, 3]) `otimes` dual (free [5, 6])

w :: GE (B `TensorSpace` A)
w = ge $ free [10, 11] `otimes` free [9, 20]

tens :: GE (A `TensorSpace` DualSpace X)
[tensor| tens^a_x = s w^ba v_xb |]

main :: IO ()
main = print (matrixOf tens)


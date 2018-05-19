{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType #-}
module Operations where

import Classes
import InstanceWrangler
import Data.Constraint
import Language.Haskell.TH

toDoubleDual' =
  unrunit >>> rmap coev >>> unassoc >>> lmap (braid >>> ev) >>> lunit

fromDoubleDual' =
  runit <<< rmap (ev <<< braid) <<< assoc <<< lmap coev <<< unlunit

dualTensor' =
  unrunit >>> rmap coev >>> unassoc >>> unrunit >>> rmap coev >>>
    unassoc >>> lmap (assoc >>> rmap braid >>> unassoc) >>> assoc >>>
    lmap (assoc >>> ev) >>> lunit

tensorDual' =
  runit <<< rmap (ev <<< braid) <<< assoc <<< runit <<< rmap (ev <<< braid) <<<
    assoc <<< lmap (unassoc <<< rmap braid <<< assoc) <<< unassoc <<<
    lmap (unassoc <<< braid <<< coev) <<< unlunit

return [] -- necessary to delimit the declaration group

toDoubleDual :: (CompactClosed cat o p i d, o a) => a `cat` d (d a)
toDoubleDual = $(wrangle 'toDoubleDual')

fromDoubleDual :: (CompactClosed cat o p i d, o a) => d (d a) `cat` a
fromDoubleDual = $(wrangle 'fromDoubleDual')

dualTensor :: (CompactClosed cat o p i d, o a, o b) =>
  d (a `p` b) `cat` (d a `p` d b)
dualTensor = $(wrangle 'dualTensor')

tensorDual :: (CompactClosed cat o p i d, o a, o b) =>
   (d a `p` d b) `cat` d (a `p` b)
tensorDual = $(wrangle 'tensorDual')


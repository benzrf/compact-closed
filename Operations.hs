{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
module Operations where

import Classes
import Data.Constraint

toDoubleDual :: forall cat o p i d a. (CompactClosed cat o p i d, o a) =>
  a `cat` d (d a)
toDoubleDual = case distr1 :: o a :- o (d a) of
  Sub Dict -> case distr1 :: o (d a) :- o (d (d a)) of
    Sub Dict ->
      unrunit >>> rmap coev >>> unassoc >>> lmap (braid >>> ev) >>> lunit


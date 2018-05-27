{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
module CompactClosed.InstanceWrangler where

import CompactClosed.Classes
import Control.Monad
import Data.Constraint
import Language.Haskell.TH

wrangle :: Name -> ExpQ
wrangle nm = do
  VarI _ (ForallT binds cxt ret) _ <- reify nm
  let (cat, o, p, i, d):_ = [(cat, o, p, i, d) |
        ConT cc `AppT` cat `AppT` o `AppT` p `AppT` i `AppT` d <- cxt,
        cc == ''CompactClosed]
      (cxt', def) = foldM wrap (varE nm) cxt

      wrap :: ExpQ -> Type -> ([Pred], ExpQ)
      wrap b (o' `AppT` x) | o' == o = provide x b
      wrap b c = ([c], b)

      provide :: Type -> ExpQ -> ([Pred], ExpQ)
      provide (p' `AppT` x `AppT` y) b | p' == p =
        provide x =<< provide y
        [| case distr2 :: ($(pure o) $(pure x), $(pure o) $(pure y)) :-
                  $(pure o) ($(pure p) $(pure x) $(pure y)) of
             Sub Dict -> $b |]
      provide (d' `AppT` x) b | d' == d = provide x
        [| case distr1 :: $(pure o) $(pure x) :-
                  $(pure o) ($(pure d) $(pure x)) of
             Sub Dict -> $b |]
      provide t b = ([o `AppT` t], b)

      ty = ForallT binds cxt' ret

  scratch <- newName "wrangled"
  letE [
    sigD scratch (pure ty),
    valD (varP scratch) (normalB def) []]
    (varE scratch)


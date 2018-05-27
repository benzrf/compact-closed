{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module AIN where

import Classes
import Control.Applicative
import Control.Monad.State
import Data.Char
import Data.List
import Data.List.NonEmpty (NonEmpty(..), (<|))
import Data.Map (Map)
import Data.Semigroup
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Operations
import qualified Data.List.NonEmpty as N
import qualified Data.Map as M

data Variance = Lower | Upper deriving (Show, Eq, Ord)
type Index = (Char, Variance)
type AINTensor = (String, [Index])
type AINDef = (AINTensor, [AINTensor])

-- parsing

pop :: MonadState [a] m => m (Maybe a)
pop = state go
  where go [] = (Nothing, [])
        go (x:xs) = (Just x, xs)

type P = StateT String Maybe

ws :: P ()
ws = void . state $ break (not . isSpace)

parseTensor :: P AINTensor
parseTensor = do
  nm <- state (break (\c -> isSpace c || c `elem` "_^"))
  guard (not (null nm))
  let step variance ixes = do
        mc <- pop
        case mc of
          Nothing -> return ixes
          Just c | isSpace c -> return ixes
          Just '_' -> step Lower ixes
          Just '^' -> step Upper ixes
          Just c -> step variance ((c, variance):ixes)
  ixes <- step Lower []
  return (nm, reverse ixes)

parseTensors :: P [AINTensor]
parseTensors = many (ws >> parseTensor)

parseDef :: P AINDef
parseDef = do
  ws
  out <- parseTensor
  ws
  pop >>= guard . (== Just '=')
  ws
  prod <- parseTensors
  ws
  pop >>= guard . (== Nothing)
  return (out, prod)

-- main logic

data TensorFactor = Scalar | ContractionIx Index | Output Int
  deriving (Show, Eq, Ord)
type TensorExp = (ExpQ, NonEmpty TensorFactor)

-- TODO maybe verify matching variances for better error messages
tensorExp :: AINTensor -> AINTensor -> TensorExp
tensorExp (_, outIxes) (nm, ixes) = (dyn nm, sig ixes)
  where sig []     = pure Scalar
        sig (i:is) = fmap factor (i:|is)
        factor i@(c, _) =
          case findIndex (\(c', _) -> c' == c) outIxes of
            Nothing -> ContractionIx i
            Just n -> Output n

-- TODO: newtypes or datas instead of all these tuples; newtypes to distinguish
-- what kind of thing an ExpQ is supposed to be holding.

infixr 5 :<|
pattern h:<|t <- h:|(N.nonEmpty -> Just t)
pattern Single x = x:|[]

reassoc :: NonEmpty TensorFactor -> ExpQ
reassoc (Single _) = [| id' |]
reassoc (_:<|t) = [| assoc >>> rmap $(reassoc t) |]

bubble1 :: NonEmpty TensorFactor -> (NonEmpty TensorFactor, ExpQ)
bubble1 (a:<|b:<|sig) | a > b = (b <| a <| sig', e')
  where (sig', e) = bubble1 sig
        e' = [| unassoc >>> bimap braid $e >>> assoc |]
bubble1 (a:|[b]) | a > b = (b:|[a], [| braid |])
bubble1 (a:<|sig) = (a <| sig', e')
  where (sig', e) = bubble1 sig
        e' = [| rmap $e |]
bubble1 sig@(Single _) = (sig, [| id' |])

bubble :: NonEmpty TensorFactor -> ExpQ -> (NonEmpty TensorFactor, ExpQ)
bubble sig e
  | sig' == sig = (sig, e)
  | otherwise = bubble sig' [| $e >>> $e' |]
  where (sig', e') = bubble1 sig

-- Only feed this a sorted signature if you want everything to work right!
-- TODO there's probably a way to make the sorting-based invariants more
-- manifest
collapse :: NonEmpty TensorFactor -> ExpQ -> (NonEmpty TensorFactor, ExpQ)
collapse (Scalar:<|sig) e = collapse sig [| $e >>> lunit |]
collapse (ContractionIx (c, Lower):<|ContractionIx (c', Upper):<|sig) e
  | c' == c = collapse (Scalar <| sig) [| $e >>> unassoc >>> lmap ev |]
collapse sig e = (sig, e)

-- TODO validation
infixr `contract`
contract :: TensorExp -> TensorExp -> TensorExp
contract (eS, sigS) (eT, sigT) = (contractedE, contractedSig)
  where prodE = [| unrunit >>> bimap $eS $eT >>> $(reassoc sigS) |]
        (sortedSig, sortedE) = bubble (sigS <> sigT) prodE
        (contractedSig, contractedE) = collapse sortedSig sortedE

-- main frontend
-- TODO proper errors
tensorQuoteDec :: String -> DecsQ
tensorQuoteDec def = [d| $(varP (mkName nm)) = $e |]
  where Just (out@(nm, _), ain) = evalStateT parseDef def
        texps = map (tensorExp out) ain
        (e, sig) | null texps = ([| id' |], pure Scalar)
                 | otherwise = foldr1 contract texps

tensor :: QuasiQuoter
tensor = QuasiQuoter {
    quoteExp  = error msg,
    quotePat  = error msg,
    quoteType = error msg,
    quoteDec  = tensorQuoteDec
  }
  where msg = "The tensor quasiquoter only supports declarations"


{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
module AIN where

import IPPrint.Colored
import Classes
import Operations
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as M
import Data.List
import Data.Char
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

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
  out <- parseTensor
  ws
  pop >>= guard . (== Just '=')
  ws
  prod <- parseTensors
  ws
  pop >>= guard . (== Nothing)
  return (out, prod)

-- main logic

data TensorFactor = ContractionIx Index | Scalar | Output Int
  deriving (Show, Eq, Ord)
data TensorSig = Factor TensorFactor | Prod TensorSig TensorSig
  deriving Show
type TensorExp = (ExpQ, TensorSig)

-- TODO maybe verify matching variances for better error messages
tensorExp :: AINTensor -> AINTensor -> TensorExp
tensorExp (_, outIxes) (nm, ixes) = (dyn nm, sig ixes)
  where sig [] = Factor Scalar
        sig [i] = factor i
        sig (i:is) = factor i `Prod` sig is
        factor i@(c, _) = Factor $
          case findIndex (\(c', _) -> c' == c) outIxes of
            Nothing -> ContractionIx i
            Just n -> Output n

contractionExp :: AINTensor -> [AINTensor] -> TensorExp
contractionExp out [] = ([| id |], Factor Scalar)
contractionExp out [t] = tensorExp out t
contractionExp out (t:ts) = ([| $e `bimap` $e' |], sig `Prod` sig')
  where (e, sig) = tensorExp out t
        (e', sig') = contractionExp out ts

-- TODO validation
contract :: TensorExp -> TensorExp -> TensorExp
contract (eS, sigS) (eT, sigT) = prod
  where prod = ([| unrunit >>> bimap $eS $eT |], sigS `Prod` sigT)


testAIN = "tens_x^a = s v_x^b w^ba"
test = s `contract` (v `contract` w)
  where Just (out, ain) = evalStateT parseDef testAIN
        exps = map (tensorExp out) ain
        [s, v, w] = exps

ppTensorExp (e, sig) = runQ $ do
  e' <- e
  runIO (print (pprint e') >> cpprint sig)

{-
goalSig :: Tensor -> TensorSig -> Maybe TensorSig
goalSig (_, ixes) sig = forM

performContractions :: TensorExp -> TensorExp
performContractions = undefined
-}


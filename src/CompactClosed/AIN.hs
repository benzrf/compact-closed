{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module CompactClosed.AIN where

import CompactClosed.Classes
import CompactClosed.Operations
import Control.Applicative hiding (many)
import Control.Monad.State
import Data.Char
import Data.List
import Data.List.NonEmpty (NonEmpty(..), (<|))
import Data.Map (Map)
import Data.Semigroup
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import qualified Data.List.NonEmpty as N
import qualified Data.Map as M
import Text.ParserCombinators.ReadP

data Variance = Lower | Upper deriving (Show, Eq, Ord)
type Index = (Char, Variance)
type AINTensor = (String, [Index])
type AINDef = (AINTensor, [AINTensor])

-- parsing

-- hmm... better be careful: index lists could easily be misparsed as tensor
-- names if the code is altered the wrong way.
parseTensor :: ReadP AINTensor
parseTensor = do
  nm <- munch1 isAlpha
  ixGrps <- many $ do
    varianceC <- satisfy (`elem` "_^")
    let variance = case varianceC of '_' -> Lower; '^' -> Upper
    ixes <- munch1 isAlpha
    return $ map (\c -> (c, variance)) ixes
  return (nm, concat ixGrps)

parseTensors :: ReadP [AINTensor]
parseTensors = parseTensor `sepBy` skipSpaces

parseDef :: ReadP AINDef
parseDef = do
  skipSpaces
  out <- parseTensor
  skipSpaces
  char '='
  skipSpaces
  prod <- parseTensors
  skipSpaces
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

compileAIN :: String -> Maybe (ExpQ, String)
compileAIN def = case readP_to_S (parseDef <* eof) def of
  [((out@(nm, _), ain), "")] -> (\e -> Just (e, nm)) $
    let texps = map (tensorExp out) ain
    in  if null texps then [| id' |]
                      else fst (foldr1 contract texps)
  _ -> Nothing

-- main frontend
-- TODO proper errors

tensorQuoteExp :: String -> ExpQ
tensorQuoteExp def = e
  where Just (e, _) = compileAIN def

tensorQuoteDec :: String -> DecsQ
tensorQuoteDec def = [d| $(varP (mkName nm)) = $e |]
  where Just (e, nm) = compileAIN def

tensor :: QuasiQuoter
tensor = QuasiQuoter {
    quoteExp  = tensorQuoteExp,
    quotePat  = error msg,
    quoteType = error msg,
    quoteDec  = tensorQuoteDec
  }
  where msg = "The tensor quasiquoter only supports " ++
          "expressions and declarations"


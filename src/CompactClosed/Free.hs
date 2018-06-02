{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
module CompactClosed.Free where

import CompactClosed.Classes
import Data.Char
import Data.Constraint
import Data.Kind
import Data.Proxy
import GHC.TypeLits
import Language.Haskell.TH hiding (Type)
import Language.Haskell.TH.Quote
import Text.ParserCombinators.ReadP

-- THIS DOES NOT ACTUALLY OBEY THE AXIOMS!!!

data FreeObj = Named Symbol | I | P FreeObj FreeObj | D FreeObj

data FreeObjV x where
  NamedV :: KnownSymbol s => FreeObjV (Named s)
  IV :: FreeObjV I
  PV :: FreeObjV x -> FreeObjV y -> FreeObjV (x `P` y)
  DV :: FreeObjV x -> FreeObjV (D x)

class O x where reflectFO :: proxy x -> FreeObjV x
instance KnownSymbol s => O (Named s) where
  reflectFO _ = NamedV
instance O I where
  reflectFO _ = IV
instance (O x, O y) => O (P x y) where
  reflectFO _ = PV (reflectFO @x Proxy) (reflectFO @y Proxy)
instance O x => O (D x) where
  reflectFO _ = DV (reflectFO @x Proxy)

data Free :: FreeObj -> FreeObj -> Type where
  Labelled :: (O x, O y) => String -> Free x y

  Id :: (O x, O y) => Free x y
  (:>>>) :: Free x y -> Free y z -> Free x z

  Bimap :: Free a b -> Free x y -> Free (a `P` x) (b `P` y)

  Assoc :: (O a, O b, O c) => ((a `P` b) `P` c) `Free` (a `P` (b `P` c))
  Unassoc :: (O a, O b, O c) => (a `P` (b `P` c)) `Free` ((a `P` b) `P` c)

  Lunit :: O x => (I `P` x) `Free` x
  Unlunit :: O x => x `Free` (I `P` x)
  Runit :: O x => (x `P` I) `Free` x
  Unrunit :: O x => x `Free` (x `P` I)

  Braid :: (O a, O b) => (a `P` b) `Free` (b `P` a)
  Unbraid :: (O a, O b) => (b `P` a) `Free` (a `P` b)

  Ev :: O a => (D a `P` a) `Free` I
  Coev :: O a => I `Free` (a `P` D a)
type FreeEndo x = Free x x

deriving instance Show (Free x y)

instance Category Free O where
  id' = Id
  (>>>) = (:>>>)

instance Distr2 O P where distr2 = Sub Dict
instance Bifunctor Free O P where
  bimap = Bimap

instance Monoidal Free O P I where
  assoc = Assoc
  unassoc = Unassoc

  lunit = Lunit
  unlunit = Unlunit

  runit = Runit
  unrunit = Unrunit

instance Braided Free O P I where
  braid = Braid
  unbraid = Unbraid

instance Symmetric Free O P I

instance Distr1 O D where distr1 = Sub Dict
instance CompactClosed Free O P I D where
  ev = Ev
  coev = Coev

freeQuoteType :: String -> TypeQ
freeQuoteType ty = [t| Free $dom $cod |]
  where [((dom, cod), "")] = readP_to_S (parseTy <* eof) ty
        parseTy = do
          -- I suppose this is why you tokenize first
          skipSpaces; dom <- parseObj
          skipSpaces; string "->"; skipSpaces
          cod <- parseObj; skipSpaces
          return (dom, cod)
        parseObj = chainr1 parseFactor $ do
          skipSpaces; char '⊗'; skipSpaces
          return (\a b -> [t| $a `P` $b |])
        parseFactor = do
          o <- parseNonDual; skipSpaces
          ([t| D $o |] <$ char '*') <++ return o
        parseNonDual =
          (char '(' *> parseObj <* char ')') +++
          ([t| I |] <$ char '1') +++
          ((\nm -> [t| Named $(litT (strTyLit nm)) |]) <$> munch1 isAlpha)

free :: QuasiQuoter
free = QuasiQuoter {
    quoteExp  = error msg,
    quotePat  = error msg,
    quoteType = freeQuoteType,
    quoteDec  = error msg
  }
  where msg = "The free quasiquoter only supports types"


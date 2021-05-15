{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}

module Test.Afa.BoolP where

import GHC.Generics
import Data.Functor.Classes
import Generic.Data (Generically1(..))
import Generic.Data.Orphans ()
import Data.Hashable

data BoolP p
  = LTrue
  | LFalse
  | Var Int
  | Not p
  | And [p]
  | Or [p]
  deriving (Functor, Foldable, Traversable, Eq, Generic, Generic1, Hashable, Show)
  deriving Eq1 via (Generically1 BoolP)
  deriving Show1 via (Generically1 BoolP)

data Plate p p' f = Plate
  { pLTrue :: forall p'. () -> f (BoolP p')
  , pLFalse :: forall p'. () -> f (BoolP p')
  , pVar :: forall p'. Int -> f (BoolP p')
  , pNot :: p -> f (BoolP p')
  , pAnd :: [p] -> f (BoolP p')
  , pOr :: [p] -> f (BoolP p')
  }

plateBase :: Applicative f => Plate p p f
plateBase = Plate
  { pLTrue = \() -> pure LTrue
  , pLFalse = \() -> pure LFalse
  , pVar = pure . Var
  , pNot = pure . Not
  , pAnd = pure . And
  , pOr  = pure . Or
  }

applyPlate :: Plate p p' f -> BoolP p -> f (BoolP p')
applyPlate Plate{pLTrue, pLFalse, pVar, pNot, pAnd, pOr} = \case
  LTrue -> pLTrue ()
  LFalse -> pLFalse ()
  Var i -> pVar i
  Not p -> pNot p
  And ps -> pAnd ps
  Or ps -> pOr ps

data ChildMod p p' f = ChildMod
  { lP :: p -> f p'
  , lVar :: Int -> f Int
  }

pureChildMod :: Applicative f => ChildMod p p f
pureChildMod = ChildMod{ lP = pure, lVar = pure }

childModToPlate :: Applicative f => ChildMod p p' f -> Plate p p' f
childModToPlate ChildMod{lP, lVar} = plateBase
  { pVar = fmap Var . lVar
  , pNot = fmap Not . lP
  , pAnd = fmap And . traverse lP 
  , pOr  = fmap Or . traverse lP 
  }

modChilds :: Applicative f => ChildMod p p' f -> BoolP p -> f (BoolP p')
modChilds = applyPlate . childModToPlate

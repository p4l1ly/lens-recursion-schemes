{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}

module Test.Afa.Term where

import GHC.Generics
import Data.Functor.Classes
import Generic.Data (Generically1(..))
import Generic.Data.Orphans ()
import Data.Hashable

data Term p q t
  = LTrue
  | P p
  | Q q
  | And [t]
  | Or [t]
  deriving (Functor, Foldable, Traversable, Eq, Generic, Generic1, Hashable, Show)
  deriving Eq1 via (Generically1 (Term p q))
  deriving Show1 via (Generically1 (Term p q))

data Plate p q t p' q' t' f = Plate
  { pLTrue :: forall p' q' t'. () -> f (Term p' q' t')
  , pP :: forall q' t'. p -> f (Term p' q' t')
  , pQ :: forall p' t'. q -> f (Term p' q' t')
  , pAnd :: forall p' q'. [t] -> f (Term p' q' t')
  , pOr :: forall p' q'. [t] -> f (Term p' q' t')
  }

plateBase :: Applicative f => Plate p q t p q t f
plateBase = Plate
  { pLTrue = \() -> pure LTrue
  , pP     = \p -> pure$ P p
  , pQ     = \q -> pure$ Q q
  , pAnd   = \ts -> pure$ And ts
  , pOr    = \ts -> pure$ Or ts
  }

applyPlate :: Plate p q t p' q' t' f -> Term p q t -> f (Term p' q' t')
applyPlate Plate{pLTrue, pP, pQ, pAnd, pOr} = \case
  LTrue -> pLTrue ()
  P p -> pP p
  Q q -> pQ q
  And ts -> pAnd ts
  Or ts -> pOr ts

data ChildMod p q t p' q' t' f = ChildMod
  { lP :: p -> f p'
  , lQ :: q -> f q'
  , lT :: t -> f t'
  }

pureChildMod :: Applicative f => ChildMod p q t p q t f
pureChildMod = ChildMod{ lP = pure, lQ = pure, lT = pure }

childModToPlate :: Applicative f => ChildMod p q t p' q' t' f -> Plate p q t p' q' t' f
childModToPlate ChildMod{lP, lQ, lT} = plateBase
  { pP   = \p -> P <$> lP p
  , pQ   = \q -> Q <$> lQ q
  , pAnd = \ts -> And <$> traverse lT ts
  , pOr  = \ts -> Or <$> traverse lT ts
  }

modChilds :: Applicative f
  => ChildMod p q t p' q' t' f -> Term p q t -> f (Term p' q' t')
modChilds = applyPlate . childModToPlate

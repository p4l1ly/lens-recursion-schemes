{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}

module Control.RecursionSchemes.Multiplate where

import Control.Monad.Identity
import Data.Fix
import Data.Generics.Multiplate
import Relude ((!!?))

data Term p q t
  = LTrue
  | P p
  | Q q
  | And [t]
  | Or [t]
  deriving (Show, Functor, Foldable, Traversable)

data Plate p q t p' q' t' f = Plate
  { pLTrue :: forall p' q' t'. () -> f (Term p' q' t')
  , pP :: forall q' t'. p -> f (Term p' q' t')
  , pQ :: forall p' t'. q -> f (Term p' q' t')
  , pAnd :: forall p' q'. [t] -> f (Term p' q' t')
  , pOr :: forall p' q'. [t] -> f (Term p' q' t')
  }

myTerm :: Term Int Int Int
myTerm = And [0, 3, 1]

ps = [1, 2, 3 :: Int]
qs = ["q1", "q2", "q3" :: String]
ts = [1.0, 2.0, 3.0 :: Double]

myPlate :: Plate Int Int Int Int String Double Maybe
myPlate = Plate
  { pLTrue = \() -> pure LTrue
  , pP     = \i -> P <$> ps !!? i
  , pQ     = \i -> Q <$> qs !!? i
  , pAnd   = \ixs -> And <$> traverse (ts !!?) ixs
  , pOr    = \ixs -> Or <$> traverse (ts !!?) ixs
  }

termPlateBase :: Applicative f => Plate p q t p q t f
termPlateBase = Plate
  { pLTrue = \() -> pure LTrue
  , pP     = \i -> pure$ P i
  , pQ     = \i -> pure$ Q i
  , pAnd   = \ixs -> pure$ And ixs
  , pOr    = \ixs -> pure$ Or ixs
  }

myPlate2 :: Plate p Int t p String t Maybe
myPlate2 = termPlateBase{pQ = \i -> Q <$> qs !!? i}

data TermAlg p q t p' q' t' f = TermAlg
  { lP :: p -> f p'
  , lQ :: q -> f q'
  , lT :: t -> f t'
  }

termAlg2Plate :: Applicative f => TermAlg p q t p' q' t' f -> Plate p q t p' q' t' f
termAlg2Plate TermAlg{lP, lQ, lT} = termPlateBase
  { pP     = \p -> P <$> lP p
  , pQ     = \q -> Q <$> lQ q
  , pAnd   = \ts -> And <$> traverse lT ts
  , pOr    = \ts -> Or <$> traverse lT ts
  }

pureTermAlg :: Applicative f => TermAlg p q t p q t f
pureTermAlg = TermAlg
  { lP = pure
  , lQ = pure
  , lT = pure
  }

myPlate3 :: Plate p Int t p String t Maybe
myPlate3 = termAlg2Plate pureTermAlg{lQ = (qs !!?)}

recTerm :: Fix (Term Int Int)
recTerm = Fix$ And [Fix LTrue, Fix LTrue]

ttcata :: Monad f => (Term p q a -> f a) -> TermAlg p q (Fix (Term p q)) p q a f
ttcata alg = pureTermAlg
  { lT = \(Fix tt) -> term (termAlg2Plate (ttcata alg)) tt >>= alg }

term :: Plate p q t p' q' t' f -> Term p q t -> f (Term p' q' t')
term plate LTrue = pLTrue plate ()
term plate (P p) = pP plate p
term plate (Q q) = pQ plate q
term plate (And ts) = pAnd plate ts
term plate (Or ts) = pOr plate ts

alg :: Term p q Int -> Identity Int
alg LTrue = pure 1
alg (And xs) = pure$ sum xs

-- type Projector p a = forall f. p f -> a -> f a 

-- mkPlate'
--   :: (forall a b. (forall f. (Plate p q t p' q' t') f -> a -> f b) -> a -> f b)
--   -> Plate p q t p' q' t' f
-- mkPlate' build = Plate
--   { pLTrue = \() -> build term LTrue
--   , pP     = undefined -- \p -> build term (P p)
--   , pQ     = undefined -- \q -> build term (Q q)
--   , pAnd   = undefined -- \ts -> build term (And ts)
--   , pOr    = undefined -- \ts -> build term (Or ts)
--   }

-- purePlate' :: Applicative f => Plate p q t p q t f
-- purePlate' = mkPlate' (\_ -> pure)

-- instance Multiplate (Plate p q (Fix (Term p q))) where
--   multiplate plate = Plate
--     { pLTrue = \() -> pure LTrue
--     , pP     = \p -> pure (P p)
--     , pQ     = \q -> pure (Q q)
--     , pAnd   = \ts -> And <$> for ts ((Fix <$>) . term plate . unFix)
--     , pOr    = \ts -> Or <$> for ts ((Fix <$>) . term plate . unFix)
--     }
--   mkPlate = mkPlate'

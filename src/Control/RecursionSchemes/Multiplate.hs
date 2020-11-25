{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}

module Control.RecursionSchemes.Multiplate where

import Control.Category ((>>>))
import Control.Monad ((>=>))
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Fix hiding (cata)
import Relude ((!!?))

data Term p q t
  = LTrue
  | P p
  | Q q
  | And [t]
  | Or [t]
  deriving (Show, Functor, Foldable, Traversable)

data TermPlate p q t p' q' t' f = TermPlate
  { pLTrue :: forall p' q' t'. () -> f (Term p' q' t')
  , pP :: forall q' t'. p -> f (Term p' q' t')
  , pQ :: forall p' t'. q -> f (Term p' q' t')
  , pAnd :: forall p' q'. [t] -> f (Term p' q' t')
  , pOr :: forall p' q'. [t] -> f (Term p' q' t')
  }

data EitherPlate a b a' b' f = EitherPlate
  { pLeft :: forall b'. a -> f (Either a' b')
  , pRight :: forall a'. b -> f (Either a' b')
  }

eitherPlateBase :: Applicative f => EitherPlate a b a b f
eitherPlateBase = EitherPlate
  { pLeft = \a -> pure$ Left a
  , pRight = \b -> pure$ Right b
  }

data EitherAlg a b a' b' f = EitherAlg
  { lLeft :: a -> f a'
  , lRight :: b -> f b'
  }

pureEitherAlg :: Applicative f => EitherAlg a b a b f
pureEitherAlg = EitherAlg
  { lLeft = pure
  , lRight = pure
  }

eitherAlg2Plate :: Functor f => EitherAlg a b a' b' f -> EitherPlate a b a' b' f
eitherAlg2Plate EitherAlg{lLeft, lRight} = EitherPlate
  { pLeft = fmap Left . lLeft
  , pRight = fmap Right . lRight
  }

applyEitherPlate :: EitherPlate a b a' b' f -> Either a b -> f (Either a' b')
applyEitherPlate EitherPlate{pLeft, pRight} = \case
  (Left a) -> pLeft a
  (Right a) -> pRight a

myTerm :: Term Int Int Int
myTerm = And [0, 3, 1]

ps = [1, 2, 3 :: Int]
qs = ["q1", "q2", "q3" :: String]
ts = [1.0, 2.0, 3.0 :: Double]

myPlate :: TermPlate Int Int Int Int String Double Maybe
myPlate = TermPlate
  { pLTrue = \() -> pure LTrue
  , pP     = \i -> P <$> ps !!? i
  , pQ     = \i -> Q <$> qs !!? i
  , pAnd   = \ixs -> And <$> traverse (ts !!?) ixs
  , pOr    = \ixs -> Or <$> traverse (ts !!?) ixs
  }

termPlateBase :: Applicative f => TermPlate p q t p q t f
termPlateBase = TermPlate
  { pLTrue = \() -> pure LTrue
  , pP     = \p -> pure$ P p
  , pQ     = \q -> pure$ Q q
  , pAnd   = \ts -> pure$ And ts
  , pOr    = \ts -> pure$ Or ts
  }

myPlate2 :: TermPlate p Int t p String t Maybe
myPlate2 = termPlateBase{pQ = \i -> Q <$> qs !!? i}

data TermAlg p q t p' q' t' f = TermAlg
  { lP :: p -> f p'
  , lQ :: q -> f q'
  , lT :: t -> f t'
  }

termAlg2Plate :: Applicative f => TermAlg p q t p' q' t' f -> TermPlate p q t p' q' t' f
termAlg2Plate TermAlg{lP, lQ, lT} = termPlateBase
  { pP   = \p -> P <$> lP p
  , pQ   = \q -> Q <$> lQ q
  , pAnd = \ts -> And <$> traverse lT ts
  , pOr  = \ts -> Or <$> traverse lT ts
  }

pureTermAlg :: Applicative f => TermAlg p q t p q t f
pureTermAlg = TermAlg
  { lP = pure
  , lQ = pure
  , lT = pure
  }

myPlate3 :: TermPlate p Int t p String t Maybe
myPlate3 = termAlg2Plate pureTermAlg{lQ = (qs !!?)}

recTerm :: Fix (Term Int Int)
recTerm = Fix$ And [Fix$ And [Fix LTrue, Fix LTrue], Fix LTrue]

cata :: Monad f => ((tt -> f a) -> tt -> f ta) -> (ta -> f a) -> tt -> f a
cata setter alg = rec where rec = setter rec >=> alg

ttCata :: forall p q a f. Monad f => (Term p q a -> f a) -> Fix (Term p q) -> f a
ttCata alg = rec where
  rec = return . unFix
    >=> applyTermPlate (termAlg2Plate$ pureTermAlg{lT = rec})
    >=> alg

ttCata2 :: forall p q a f. Monad f => (Term p q a -> f a) -> Fix (Term p q) -> f a
ttCata2 = cata$ \rec -> applyTermPlate (termAlg2Plate$ pureTermAlg{lT = rec}) . unFix

ttAna :: Monad f => (a -> f (Term p q a)) -> a -> f (Fix (Term p q))
ttAna coalg = rec where
  rec = coalg
    >=> applyTermPlate (termAlg2Plate$ pureTermAlg{lT = rec})
    >=> return . Fix

recMTerm :: Fix (Compose (Either Int) (Term Int Int))
recMTerm = Fix$Compose$Right$ And
  [ Fix$Compose$Right$ And [Fix$Compose$Left 0, Fix$Compose$Left 1]
  , Fix$Compose$Right LTrue
  ]

ttSide :: forall p q q' f.
  Applicative f => (q -> f q') -> Fix (Term p q) -> f (Fix (Term p q'))
ttSide qf = rec where
  rec = unFix
    >>> applyTermPlate (termAlg2Plate$ pureTermAlg{lT = rec, lQ = qf})
    >>> fmap Fix

ttSideLeaf :: forall f p q t q' t'.
  Applicative f
  => (q -> f q')
  -> (t -> f t')
  -> Fix (Compose (Either t) (Term p q))
  -> f (Fix (Compose (Either t') (Term p q')))
ttSideLeaf qf tf = rec where
  rec = getCompose . unFix
    >>> ( applyEitherPlate$ eitherAlg2Plate$ EitherAlg
          { lLeft = tf
          , lRight = applyTermPlate (termAlg2Plate$ pureTermAlg{lT = rec, lQ = qf})
          }
        )
    >>> fmap (Fix . Compose)

applyTermPlate :: TermPlate p q t p' q' t' f -> Term p q t -> f (Term p' q' t')
applyTermPlate plate LTrue = pLTrue plate ()
applyTermPlate plate (P p) = pP plate p
applyTermPlate plate (Q q) = pQ plate q
applyTermPlate plate (And ts) = pAnd plate ts
applyTermPlate plate (Or ts) = pOr plate ts

alg :: Term p q Int -> Identity Int
alg LTrue = pure 1
alg (And xs) = pure$ sum xs
alg _ = error "not implemented"

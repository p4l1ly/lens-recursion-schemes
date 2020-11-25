{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}

module Main (main) where

import GHC.Generics
import Data.Functor.Classes
import Generic.Data (Generically1(..))
import Generic.Data.Orphans ()
import Test.HUnit
import Control.Lens
import Control.Monad
import Control.Monad.ST
import Data.Fix (Fix(..))
import Data.Functor.Foldable (ListF(..))
import Data.Hashable

import Control.RecursionSchemes.Lens
  ( recursion
  , sideCata
  , cata
  , recursiveSetter
  , corecursiveSetter
  , ana
  , hylo
  , hashConsOf
  , noConsOf
  , cataT
  , anaT
  , recursiveTraversal
  , corecursiveTraversal
  )

import qualified Test.Afa

-- Functor Expr
data ExprF rec = AddF rec rec | ValF Int
  deriving (Functor, Foldable, Traversable, Eq, Generic, Generic1, Hashable, Show)
  deriving Eq1 via (Generically1 ExprF)
  deriving Show1 via (Generically1 ExprF)

exprFAlg :: ExprF Int -> Int
exprFAlg (ValF i) = i
exprFAlg (AddF a b) = a + b

-- Fix Expr

pattern FAdd a b = Fix (AddF a b)
pattern FVal i = Fix (ValF i)

-- Explicit Expr

data Expr = Add Expr Expr | Val Int

exprAlg :: Setter Expr Int Expr Int
exprAlg = sets$ \eval -> \case
  Val i -> i
  Add a b -> eval a + eval b

exprAlg2 :: Setter Expr (ExprF a) Expr a
exprAlg2 = sets$ \eval -> \case
  Val i -> ValF i
  Add a b -> AddF (eval a) (eval b)

-- Functor Ors

data AndsF ors rec = AndF rec rec | OrsF {_orsF :: ors} deriving Functor
data OrsF nots rec = OrF rec rec | NotsF {_notsF :: nots} deriving Functor
data NotsF rec = NotF rec | NTrueF deriving Functor

makeLenses ''AndsF
makeLenses ''OrsF

notsFAlg :: NotsF Bool -> Bool
notsFAlg NTrueF = True
notsFAlg (NotF x) = not x

orsFAlg :: OrsF Bool Bool -> Bool
orsFAlg (NotsF x) = x
orsFAlg (OrF x y) = x || y

andsFAlg :: AndsF Bool Bool -> Bool
andsFAlg (OrsF x) = x
andsFAlg (AndF x y) = x && y

-- Fix Ors

pattern FOr a b = Fix (OrF a b)
pattern FNots x = Fix (NotsF x)
pattern FNot x = Fix (NotF x)
pattern FNTrue = Fix NTrueF
pattern FAnd a b = Fix (AndF a b)
pattern FOrs a = Fix (OrsF a)

-- Explicit Ors

data Ors = Or Ors Ors | Nots {_nots :: Nots}
data Nots = Not Nots | NTrue

notsAlg :: Setter Nots Bool Nots Bool
notsAlg = sets$ \eval -> \case
  NTrue -> True
  Not x -> not (eval x)

data Ors' = Or' Ors Ors | Nots' Bool

orsAlg1 :: Setter Ors Ors' Nots Bool
orsAlg1 = sets$ \eval -> \case
  Or ors1 ors2 -> Or' (ors1) (ors2)
  Nots x -> Nots' (eval x)

orsAlg2 :: Setter Ors' Bool Ors Bool
orsAlg2 = sets$ \eval -> \case
  Or' ors1 ors2 -> (eval ors1) || (eval ors2)
  Nots' x -> x


-- ListF

listFCoalg :: Int -> ListF Int Int
listFCoalg 0 = Nil
listFCoalg x = Cons x (x - 1)

listFAlg :: ListF Int Int -> Int
listFAlg Nil = 0
listFAlg (Cons x y) = x + y

-- Test definitions

check :: Counts -> IO ()
check result = do
  guard$ failures result == 0
  guard$ errors result == 0

main :: IO ()
main = (check =<<)$ runTestTT$ TestList$
  [ "nestedCata" ~: do
      assertEqual "triple" False
        $ FAnd
            (FOrs$ FNots FNTrue)
            (FOrs$ FOr (FNots$ FNot$ FNot$ FNot FNTrue) (FNots$ FNot FNTrue))
        & cata recursiveSetter
        . sets (andsFAlg .)
        . orsF
        . cata recursiveSetter
        . sets (orsFAlg .)
        . notsF
        . cata recursiveSetter
        %~ notsFAlg
  , "explicitCata" ~: do
      assertEqual "id" 14 $ Add (Val 8) (Val 6) & recursion exprAlg
      assertEqual "id" 14 $ Add (Val 8) (Val 6) & cata exprAlg %~ id
      assertEqual "f" 14 $ Add (Val 8) (Val 6) & cata exprAlg2 %~ exprFAlg
  , "functorCata" ~: do
      assertEqual "fix" 14 $ FAdd (FVal 8) (FVal 6) & cata recursiveSetter %~ exprFAlg
  , "sideCata" ~: do
      assertEqual "triple" False
        $ FAnd
            (FOrs$ FNots FNTrue)
            (FOrs$ FOr (FNots$ FNot$ FNot$ FNot FNTrue) (FNots$ FNot FNTrue))
        & sideCata (iso unFix id . orsF) (sets (andsFAlg .) . mapped)
        . sideCata (iso unFix id . notsF) (sets (orsFAlg .) . mapped)
        . cata recursiveSetter
        %~ notsFAlg
      assertEqual "explicit" False
        $ Or (Nots$ Not$ Not$ Not NTrue) (Nots$ Not NTrue)
        & sideCata orsAlg1 orsAlg2
        %~ recursion notsAlg
  , "ana" ~: do
      assertEqual "[3..0]" [3, 2, 1]
        $ 3 & ana corecursiveSetter %~ listFCoalg
  , "hylo" ~: do
      assertEqual "sum [3..0]" 6
        $ 3 & hylo mapped %~ \i -> (listFCoalg i, listFAlg)
  , "consing" ~: do
      assertEqual "hashcons" [ValF 1, AddF 0 0] $ snd$ runIdentity$
        cataT recursiveTraversal `hashConsOf` FAdd (FVal 1) (FVal 1)
      assertEqual "nocons" [ValF 1, ValF 1, AddF 0 1] $ snd$ runIdentity$
        cataT recursiveTraversal `noConsOf` FAdd (FVal 1) (FVal 1)
  , "cataT,anaT" ~: do
      assertEqual "hashcons" [1, 3, 1, 4, 2, 3, 2, 4] $
        traverseOf (cataT recursiveTraversal) (\case ValF i -> [i]; AddF a b -> [a, b])
          $ FAdd (FAdd (FVal 1) (FVal 2)) (FAdd (FVal 3) (FVal 4))

      print$
        (
          traverseOf (anaT corecursiveTraversal)
            ( \case
              0 -> [ValF 0, ValF 0]
              1 -> [ValF 1]
              x -> [AddF (x - 1) (x - 2)]
            )
            3
          :: [Fix ExprF]
        )
  , "removeOrphans" ~: do
      putStrLn "FOOOOO"
      print$ runST Test.Afa.removeOrphans
      putStrLn "FOOOOO"
      print$ runST Test.Afa.removeOrphans'
  ]

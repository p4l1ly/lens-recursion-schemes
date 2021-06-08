{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures #-}

module Control.RecursionSchemes.Utils.HashCons2 where

import Capability.State
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Hashable
import GHC.Types (Symbol)

data ConsState x k = ConsState !Int !(HashMap k Int) ![x] deriving Show

{-# INLINE consState0 #-}
consState0 :: ConsState x k
consState0 = ConsState 0 HM.empty []

{-# INLINE consState0From #-}
consState0From :: Int -> ConsState x k
consState0From i = ConsState i HM.empty []

{-# INLINE consResult #-}
consResult :: ConsState x k -> (Int, [x])
consResult (ConsState i _ xs) = (i, reverse xs)

{-# INLINABLE consK #-}
consK :: forall (tag :: Symbol) x k m.
  (HasState tag (ConsState x k) m, Eq k, Hashable k)
  => k -> x -> m Int
consK key x = do
  ConsState i hm xs <- get @tag
  let
    handleAlter = \case
      old@(Just i') -> ((i', i, xs), old)
      _ -> ((i, i + 1, x:xs), Just i)
    ((hashedIx, i', xs'), hm') = HM.alterF handleAlter key hm
  put @tag$ ConsState i' hm' xs' 
  return hashedIx


{-# INLINE cons #-}
cons :: forall (tag :: Symbol) k m.
  (HasState tag (ConsState k k) m, Eq k, Hashable k)
  => k -> m Int
cons k = consK @tag k k

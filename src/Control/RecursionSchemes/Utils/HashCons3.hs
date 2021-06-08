{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Control.RecursionSchemes.Utils.HashCons3 where

import Capability.State
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Hashable
import Data.Maybe
import GHC.Types (Symbol)

data ConsState x k = ConsState !Int !(HashMap k (x, Int)) ![k]

{-# INLINE consState0 #-}
consState0 :: ConsState x k
consState0 = ConsState 0 HM.empty []

{-# INLINE consState0From #-}
consState0From :: Int -> ConsState x k
consState0From i = ConsState i HM.empty []

{-# INLINE consResult #-}
consResult :: (Eq k, Hashable k) => ConsState x k -> (Int, [x])
consResult (ConsState i hm ks) = (i, reverse$ map (fst . (hm HM.!)) ks)

{-# INLINABLE consKMod #-}
consKMod :: forall (tag :: Symbol) x k m.
  (HasState tag (ConsState x k) m, Eq k, Hashable k)
  => k -> x -> (x -> x) -> m Int
consKMod key x mod = do
  ConsState i hm ks <- get @tag
  let
    handleAlter = \case
      Just (x0, i0) -> ((i0, i, ks), Just (mod x0, i0))
      _ -> ((i, i + 1, key:ks), Just (x, i))
    ((hashedIx, i', xs'), hm') = HM.alterF handleAlter key hm
  put @tag$ ConsState i' hm' xs' 
  return hashedIx

{-# INLINABLE consK #-}
consK :: forall (tag :: Symbol) x k m.
  (HasState tag (ConsState x k) m, Eq k, Hashable k)
  => k -> x -> m Int
consK key x = consKMod @tag key x id

{-# INLINE cons #-}
cons :: forall (tag :: Symbol) k m.
  (HasState tag (ConsState k k) m, Eq k, Hashable k)
  => k -> m Int
cons k = consKMod @tag k k id

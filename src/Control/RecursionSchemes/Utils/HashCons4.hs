{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Control.RecursionSchemes.Utils.HashCons4 where

import Data.Traversable
import Data.Foldable
import Data.Array.Base (unsafeArray, unsafeRead, unsafeWrite, getNumElements, unsafeNewArray_)
import Capability.State
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Hashable
import Data.Maybe
import Data.Array
import Data.STRef
import Data.Array.ST
import Control.Monad.ST
import GHC.Types (Symbol)
import Data.Coerce (Coercible, coerce)

import Control.RecursionSchemes.Utils.GrowableArray (GrowableArray(GrowableArray))
import qualified Control.RecursionSchemes.Utils.GrowableArray as GArray

data ConsState arr x k = ConsState !(HashMap k Int) !(GrowableArray arr x)

consState0 :: (MArray arr x m, Monad m) => m (ConsState arr x k)
consState0 = consState0Cap 0
{-# INLINE consState0 #-}

consState0Cap :: (MArray arr x m, Monad m) => Int -> m (ConsState arr x k)
consState0Cap cap = do
  arr <- GArray.new cap
  return$ ConsState HM.empty arr
{-# INLINE consState0Cap #-}

consResult :: (MArray arr x m, Monad m) => ConsState arr x k -> m (Int, [x])
consResult (ConsState hm (GrowableArray i xs)) = (i,) <$> for [0..i-1] (unsafeRead xs)
{-# INLINE consResult #-}

consKMod :: forall (tag :: Symbol) m' arr x k m.
  ( HasState tag (ConsState arr x k) m
  , Eq k, Hashable k
  , (forall a. Coercible (m' a) (m a))
  , MArray arr x m'
  )
  => k -> x -> (x -> x) -> m Int
consKMod key x mod = do
  ConsState hm xs@(GArray.size -> i) <- get @tag
  let
    handleAlter = \case
      Just i0 -> (Just i0, Just i0)
      _ -> (Nothing, Just i)
    (i0, hm') = HM.alterF handleAlter key hm

  (consState, hashedIx) <- case i0 of
    Nothing -> do
      xs' <- coerce @(m' (GrowableArray arr x))$ GArray.append x xs
      return (ConsState hm' xs', i)
    Just i0 -> do
      let xsArr = GArray.arr xs
      () <- coerce @(m' ())$ unsafeRead xsArr i0 >>= unsafeWrite xsArr i0 . mod
      return (ConsState hm' xs, i0)

  put @tag consState
  return hashedIx
{-# INLINABLE consKMod #-}

-- consK :: forall (tag :: Symbol) m' arr x k m.
--   ( HasState tag (ConsState arr x k) m
--   , Eq k, Hashable k
--   , (forall a. Coercible (m' a) (m a))
--   , MArray arr x m'
--   )
--   => k -> x -> m Int
-- consK key x = consKMod @tag @m' key x id
-- {-# INLINABLE consK #-}
-- 
-- cons :: forall (tag :: Symbol) m' arr k m.
--   (HasState tag (ConsState arr k k) m, Eq k, Hashable k, MArray arr k m)
--   => k -> m Int
-- cons k = consKMod @tag @m' k k id
-- {-# INLINE cons #-}

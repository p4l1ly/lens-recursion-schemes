{-# LANGUAGE DeriveGeneric #-}

module Control.RecursionSchemes.Utils.GrowableArray where

import Data.Foldable
import Data.Array.Base
import GHC.Generics

data GrowableArray arr a = GrowableArray {size :: Int, arr :: arr Int a}
  deriving (Generic)

new :: (MArray arr x m) => Int -> m (GrowableArray arr x)
new capacity = do
  arr <- unsafeNewArray_ (0, capacity - 1)
  return$ GrowableArray 0 arr
{-# INLINE new #-}

append :: (MArray arr x m) => x -> GrowableArray arr x -> m (GrowableArray arr x)
append x (GrowableArray size arr) = do
  let size' = size + 1
  len <- getNumElements arr
  arr' <- if size < len
    then return arr
    else do
      arr' <- unsafeNewArray_ (0, 2 * size')
      for_ [0..len - 1]$ \i -> unsafeRead arr i >>= unsafeWrite arr' i
      return arr'
  unsafeWrite arr' size x
  return$ GrowableArray size' arr'
{-# INLINE append #-}

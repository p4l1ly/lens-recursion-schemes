{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.RecursionSchemes.Utils.NoCons2 where

import Capability.State

data ConsState x k = ConsState !Int ![x]

{-# INLINE consState0 #-}
consState0 :: ConsState x k
consState0 = ConsState 0 []

{-# INLINE consState0From #-}
consState0From :: Int -> ConsState x k
consState0From i = ConsState i []

{-# INLINE consResult #-}
consResult :: ConsState x k -> (Int, [x])
consResult (ConsState i xs) = (i, reverse xs)

{-# INLINABLE cons #-}
cons ::
  (HasState "cons" (ConsState x k) m)
  => x -> m Int
cons x = do
  ConsState i xs <- get @"cons"
  put @"cons"$ ConsState (i+1) (x:xs)
  return i

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}

module Control.RecursionSchemes.Utils.HashCons
  ( HashConsT
  , runHashConsT
  , runHashConsTFrom
  , hashCons
  , hashCons'
  , hashConsOf
  )
  where

import Control.Lens
import Control.Monad.Trans.Class
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Hashable

data HashConsTData a x k = HashConsTData a !Int !(HashMap k Int) ![x]
newtype HashConsT x k m a = HashConsT
  {rawRunHashConsT_ :: Int -> HashMap k Int -> [x] -> m (HashConsTData a x k)}
instance Monad m => Functor (HashConsT x k m) where
  {-# INLINABLE fmap #-}
  fmap f (HashConsT m) = HashConsT$ \(!i) (!hm) (!xs) -> do
    HashConsTData a i' hm xs' <- m i hm xs
    return$ HashConsTData (f a) i' hm xs'
instance Monad m => Applicative (HashConsT x k m) where
  {-# INLINABLE pure #-}
  pure a = HashConsT$ \(!i) (!hm) (!xs) -> return$ HashConsTData a i hm xs
  {-# INLINABLE (<*>) #-}
  (HashConsT m1) <*> (HashConsT m2) = HashConsT$ \(!i0) (!hm0) (!xs0) -> do
    HashConsTData fa i1 hm1 xs1 <- m1 i0 hm0 xs0
    HashConsTData a i2 hm2 xs2 <- m2 i1 hm1 xs1
    return$ HashConsTData (fa a) i2 hm2 xs2
instance Monad m => Monad (HashConsT x k m) where
  {-# INLINABLE return #-}
  return = pure
  {-# INLINABLE (>>=) #-}
  (HashConsT m1) >>= getM2 = HashConsT$ \(!i0) (!hm0) (!xs0) -> do
    HashConsTData a i1 hm1 xs1 <- m1 i0 hm0 xs0
    rawRunHashConsT_ (getM2 a) i1 hm1 xs1
instance MonadTrans (HashConsT x k) where
  {-# INLINABLE lift #-}
  lift m = HashConsT$ \(!i) (!hm) (!x) -> (\a -> HashConsTData a i hm x) <$> m

{-# INLINE runHashConsTFrom #-}
runHashConsTFrom :: Monad m => Int -> HashConsT x k m a -> m (a, [x])
runHashConsTFrom i action = do
  HashConsTData a i hm xs <- rawRunHashConsT_ action i HM.empty []
  return (a, reverse xs)

{-# INLINE runHashConsT #-}
runHashConsT :: Monad m => HashConsT x k m a -> m (a, [x])
runHashConsT = runHashConsTFrom 0

{-# INLINABLE hashCons #-}
hashCons :: (Eq k, Hashable k, Monad m) => k -> x -> HashConsT x k m Int
hashCons key x = HashConsT$ \(!i) (!hm) (!xs) ->
  let
    handleAlter = \case
      old@(Just i') -> ((i', i, xs), old)
      _ -> ((i, i + 1, x:xs), Just i)
    ((hashedIx, i', xs'), hm') = HM.alterF handleAlter key hm
  in
  return$ HashConsTData hashedIx i' hm' xs' 

{-# INLINE hashCons' #-}
hashCons' :: (Eq k, Hashable k, Monad m) => k -> HashConsT k k m Int
hashCons' !k = hashCons k k

{-# INLINABLE hashConsOf #-}
hashConsOf :: (Eq fi, Hashable fi, Monad m)
  => LensLike (HashConsT fi fi m) s x fi Int -> s -> m (x, [fi])
hashConsOf setter = runHashConsT . setter hashCons'

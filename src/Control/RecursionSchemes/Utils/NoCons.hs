{-# LANGUAGE BangPatterns #-}

module Control.RecursionSchemes.Utils.NoCons
  ( NoConsT
  , runNoConsT
  , runNoConsTFrom
  , nocons
  , noConsOf
  )
  where

import Control.Lens
import Control.Monad.Trans.Class

data NoConsTData a x = NoConsTData a !Int ![x]
newtype NoConsT x m a = NoConsT {rawRunNoConsT_ :: Int -> [x] -> m (NoConsTData a x)}
instance Monad m => Functor (NoConsT x m) where
  {-# INLINABLE fmap #-}
  fmap f (NoConsT m) = NoConsT$ \(!i) (!xs) -> do
    NoConsTData a i' xs' <- m i xs
    return$ NoConsTData (f a) i' xs'
instance Monad m => Applicative (NoConsT x m) where
  {-# INLINABLE pure #-}
  pure a = NoConsT$ \(!i) (!xs) -> return$ NoConsTData a i xs
  {-# INLINABLE (<*>) #-}
  (NoConsT m1) <*> (NoConsT m2) = NoConsT$ \(!i0) (!xs0) -> do
    NoConsTData fa i1 xs1 <- m1 i0 xs0
    NoConsTData a i2 xs2 <- m2 i1 xs1
    return$ NoConsTData (fa a) i2 xs2
instance Monad m => Monad (NoConsT x m) where
  {-# INLINABLE return #-}
  return = pure
  {-# INLINABLE (>>=) #-}
  (NoConsT m1) >>= getM2 = NoConsT$ \(!i0) (!xs0) -> do
    NoConsTData a i1 xs1 <- m1 i0 xs0
    rawRunNoConsT_ (getM2 a) i1 xs1
instance MonadTrans (NoConsT x) where
  {-# INLINABLE lift #-}
  lift m = NoConsT$ \(!i) (!x) -> (\a -> NoConsTData a i x) <$> m

{-# INLINE runNoConsTFrom #-}
runNoConsTFrom :: Monad m => Int -> NoConsT x m a -> m (a, [x])
runNoConsTFrom i action = do
  NoConsTData a i xs <- rawRunNoConsT_ action i []
  return (a, reverse xs)

{-# INLINE runNoConsT #-}
runNoConsT :: Monad m => NoConsT x m a -> m (a, [x])
runNoConsT = runNoConsTFrom 0

{-# INLINABLE nocons #-}
nocons :: Monad m => x -> NoConsT x m Int
nocons x = NoConsT$ \(!i) (!xs) -> return$ NoConsTData i (i + 1) (x:xs)

{-# INLINABLE noConsOf #-}
noConsOf :: Monad m => LensLike (NoConsT fi m) s x fi Int -> s -> m (x, [fi])
noConsOf setter = runNoConsT . setter nocons

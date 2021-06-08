{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Control.RecursionSchemes.Utils.HasIxed where

import Data.Kind (Type)
import GHC.Exts (Proxy#, proxy#)
import Capability.Source
import Data.Array.Base
import Data.Coerce (Coercible, coerce)
import Data.Ix

class Monad m
  => HasIxedSource (tag :: k) (i :: Type) (a :: Type) (m :: Type -> Type)
  | tag m -> a, tag m -> i
  where
  iawait_ :: Proxy# tag -> i -> m a

iawait :: forall tag i a m. HasIxedSource tag i a m => i -> m a
iawait = iawait_ (proxy# @tag)
{-# INLINE iawait #-}

newtype IxState (m :: Type -> Type) (a :: Type) = IxState (m a)
  deriving (Functor, Applicative, Monad)

newtype IxStateUnsafe (m' :: Type -> Type) (m :: Type -> Type) (a :: Type) = IxStateUnsafe (m a)
  deriving (Functor, Applicative, Monad)

instance
  ( HasSource tag (arr i a) m
  , Coercible (m' a) (m a)
  , MArray arr a m'
  , Ix i
  )
  => HasIxedSource tag Int a (IxStateUnsafe m' m) where
  iawait_ _ i = do
    arr :: arr i a <- coerce @(m (arr i a))$ await @tag
    coerce @(m' a)$ unsafeRead arr i
  {-# INLINE iawait_ #-}

instance (HasSource tag (arr i a) m, MArray arr a m, Ix i) => HasIxedSource tag i a (IxState m) where
  iawait_ _ i = coerce @(m a)$ do
    arr <- await @tag
    readArray arr i
  {-# INLINE iawait_ #-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Control.RecursionSchemes.Lens where

import Data.Functor.Compose
import Control.Monad.Cont
import Control.Monad.State
import Control.Monad.Writer
import Control.Arrow
import Control.Lens
import Data.Functor.Foldable (Recursive, Corecursive, Base, project, embed)
import Data.Array
import Data.Array.Unsafe
import Data.Array.ST
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as M
import Data.Hashable
import Control.Monad.ST

-- Standard recursion

recursion :: Setter t a t a -> t -> a
recursion setter = rec where rec = setter %~ rec

sideCata
  :: ASetter t1 t1' t2 a
  -> ASetter t1' a t1 a
  -> Setter t1 a t2 a
sideCata t1t2 t1t1 = sets$ \eval -> let rec = t1t2 %~ eval >>> t1t1 %~ rec in rec

recur :: Setter ta tb a b -> Setter a b (ta -> tb, a) b
recur setter = sets$ \eval -> let rec = curry eval$ setter %~ rec in rec

recur2cata apply alg (tt2ta, tt) = alg `apply` tt2ta tt
recur2ana apply coalg (ta2tt, a) = ta2tt `apply` coalg a

cata :: Setter tt ta tt a -> Setter tt a ta a
cata setter = recur setter . sets (recur2cata ($))

ana :: Setter ta tt a tt -> Setter a tt a ta
ana setter = recur setter . sets (recur2ana ($))

recurT :: forall m ta tb a b. Monad m =>
  LensLike m ta tb a b -> LensLike m a b (ta -> m tb, a) b
recurT setter eval = rec where rec = curry eval$ traverseOf setter rec

cataT :: Monad m => LensLike m tt ta tt a -> LensLike m tt a ta a
cataT setter = recurT setter . recur2cata (=<<)

anaT :: Monad m => LensLike m ta tt a tt -> LensLike m a tt a ta
anaT setter = recurT setter . recur2ana (=<<)

-- Ixed recursion

recurScan ::
  ( Functor f
  , Ixed (f a)
  , Ixed (f b)
  , i ~ Index (f a)
  , i ~ Index (f b)
  , a ~ IxValue (f a)
  , b ~ IxValue (f b)
  )
  => Setter ti tb i b -> Setter (f a) (f b) (ti -> tb, a) b
recurScan setter = sets$ \eval arr ->
  let arr' = fmap (curry eval$ setter %~ \i -> arr' ^?! ix i) arr in arr'

cataScan ::
  ( Functor f
  , Ixed (f a)
  , Ixed (f ti)
  , i ~ Index (f a)
  , i ~ Index (f ti)
  , a ~ IxValue (f a)
  , ti ~ IxValue (f ti)
  )
  => Setter ti ta i a -> Setter (f ti) (f a) ta a
cataScan setter = recurScan setter . sets (recur2cata ($))

anaScan ::
  ( Functor f
  , Ixed (f a)
  , Ixed (f t)
  , ix ~ Index (f a)
  , ix ~ Index (f t)
  , a ~ IxValue (f a)
  , t ~ IxValue (f t)
  )
  => Setter ta t ix t -> Setter (f a) (f t) a ta
anaScan setter = recurScan setter . sets (recur2ana ($))

-- MArray recursion

recurScanT :: forall s mt i ti tb a b.
  (MonadTrans mt, Monad (mt (ST s)), Ix i)
  => LensLike (ST s) ti tb i b
  -> LensLike (mt (ST s)) (Array i a) (Array i b) (ti -> ST s tb, a) b
recurScanT setter eval as = do
  let bnds = bounds as
  (bs :: STArray s i b) <- lift$ newArray_ bnds
  forM_ (assocs as)$ \(i, a) -> do
    b <- eval$ (, a)$ traverseOf setter$ readArray bs
    lift$ writeArray bs i b
  lift$ unsafeFreeze bs

cataScanT ::
  (MonadTrans mt, Monad (mt (ST s)), Ix i)
  => LensLike (ST s) ti ta i a
  -> LensLike (mt (ST s)) (Array i ti) (Array i a) ta a
cataScanT setter = recurScanT setter . \alg (ti2ta, ti) -> alg =<< lift (ti2ta ti)

anaScanT ::
  (MonadTrans mt, Monad (mt (ST s)), Ix i)
  => LensLike (ST s) ta t i t
  -> LensLike (mt (ST s)) (Array i a) (Array i t) a ta
anaScanT setter = recurScanT setter . \coalg (ti2ta, ti) -> lift . ti2ta =<< coalg ti


-- MArray better ana

anaScanT2 :: forall mt i g tgi arr m tgi'.
  (MonadTrans mt, Monad (mt m), Ix i, Monoid g, MArray arr g m)
  => LensLike m tgi tgi' (g, i) (g, i)
  -> LensLike (mt m) (arr i g) [tgi'] g tgi
anaScanT2 setter eval gs = do
  bnds <- lift$ getBounds gs
  (reverse <$>) . forM (reverse$ range bnds)$ \i -> do
    g <- lift$ readArray gs i
    tgi <- eval g
    lift$ flip (traverseOf setter) tgi$ \(gj, j) -> do
      gj0 <- readArray gs j
      let gj' = gj0 <> gj
      writeArray gs j gj'
      return (gj', j)

recurScanT2 :: forall mt i g tgi arr m tb b.
  (MonadTrans mt, Monad (mt m), Ix i, Monoid g, MArray arr g m, MArray arr b m)
  => LensLike (BeforeAfter m m) tgi tb (g, i) b
  -> LensLike (mt m) (arr i g) (arr i b) (tgi -> mt m tb, (g, i)) b
recurScanT2 setter eval gs = do
  bnds <- lift$ getBounds gs
  bs <- lift$ newArray_ bnds

  let
    step :: [i] -> mt m () -> mt m ()
    step [] previousStep = previousStep
    step (i:rest) previousStep = do
      step rest$ do
        g <- lift$ readArray gs i
        b <- eval$ (, (g, i))$ \tgi -> do
          let
            BeforeAfter before after =
              flip (traverseOf setter) tgi$ \(gj, j) -> BeforeAfter
                (readArray gs j >>= writeArray gs j . (gj <>))
                (readArray bs j)
          lift before
          previousStep
          lift after
        lift$ writeArray bs i b

  step (range bnds) (return ())
  return bs

recurScanT3 :: forall mt i g tgi arr m tb b r.
  (MonadTrans mt, Monad (mt m), Ix i, Monoid g, MArray arr g m, MArray arr b m)
  => LensLike (BeforeAfter m m) tgi tb (g, i) b
  -> LensLike (ContT r (mt m)) (arr i g) (arr i b) (tgi -> ContT r (mt m) tb, (g, i)) b
recurScanT3 setter eval gs = do
  bnds <- lift$lift$ getBounds gs
  bs <- lift$lift$ newArray_ bnds

  let
    step :: [i] -> ContT r (mt m) () -> ContT r (mt m) ()
    step [] previousStep = previousStep
    step (i:rest) previousStep = do
      step rest$ do
        g <- lift$lift$ readArray gs i
        b <- callCC$ \exitWrite -> do
          continue <- callCC$ \exitToPrevious -> do
            b <- eval$ (, (g, i))$ \tgi -> do
              let
                BeforeAfter before after =
                  flip (traverseOf setter) tgi$ \(gj, j) -> BeforeAfter
                    (readArray gs j >>= writeArray gs j . (gj <>))
                    (readArray bs j)
              lift$lift$ before
              callCC exitToPrevious
              lift$lift$ after
            exitWrite b
          previousStep
          continue ()
        lift$lift$ writeArray bs i b

  step (range bnds) (return ())
  return bs

data BeforeAfter m1 m2 a = BeforeAfter (m1 ()) (m2 a)
instance Functor m2 => Functor (BeforeAfter m1 m2) where
  fmap fn (BeforeAfter before after) = BeforeAfter before (fn <$> after)
instance (Applicative m1, Applicative m2) => Applicative (BeforeAfter m1 m2) where
  pure x = BeforeAfter (pure ()) (pure x)
  BeforeAfter bef1 fab <*> BeforeAfter bef2 fa =
    BeforeAfter (bef1 *> bef2) (fab <*> fa)

-- Building Arrays (NoCons)

newtype NoConsT x m a = NoConsT (StateT Int (WriterT (Endo [x]) m) a)
  deriving (Functor, Applicative, Monad)
instance MonadTrans (NoConsT x) where
  lift = NoConsT . lift . lift

runNoConsT :: Monad m => NoConsT x m a -> m (a, [x])
runNoConsT (NoConsT action) =
  fmap (second (`appEndo` []))$ runWriterT$ evalStateT action 0

nocons :: Monad m => x -> NoConsT x m Int
nocons x = do
  nextIx <- NoConsT get
  NoConsT$ tell$ Endo (x:)
  NoConsT$ put$ succ nextIx
  return nextIx

noConsOf :: Monad m => LensLike (NoConsT fi m) s x fi Int -> s -> m (x, [fi])
noConsOf setter = runNoConsT . setter nocons

-- Building Arrays (HashCons)

newtype HashConsT x k m a = HashConsT
  (StateT (Int, HashMap k Int) (WriterT (Endo [x]) m) a)
  deriving (Functor, Applicative, Monad)
instance MonadTrans (HashConsT x k) where
  lift = HashConsT . lift . lift

runHashConsT :: Monad m => HashConsT x k m a -> m (a, [x])
runHashConsT (HashConsT action) = do
  (a, xs) <- runWriterT$ evalStateT action (0, M.empty)
  return (a, xs `appEndo` [])

hashCons :: (Eq k, Hashable k, Monad m) => k -> x -> HashConsT x k m Int
hashCons key x = HashConsT$ do
  (nextIx, hash) <- get
  ((hashedIx, nextIx'), hash') <- lift$ getCompose$
    M.alterF (handleAlter x nextIx) key hash
  put (nextIx', hash')
  return hashedIx
  where
  handleAlter t i = \case
    old@(Just i') -> Compose$ return ((i', i), old)
    _ -> Compose$ do
      tell$ Endo (t:)
      return ((i, i + 1), Just i)

hashCons' :: (Eq k, Hashable k, Monad m) => k -> HashConsT k k m Int
hashCons' k = hashCons k k

hashConsOf :: (Eq fi, Hashable fi, Monad m)
  => LensLike (HashConsT fi fi m) s x fi Int -> s -> m (x, [fi])
hashConsOf setter = runHashConsT . setter hashCons'

-- Specialization for the recursion-schemes (and other) library compatibility

recursiveSetter :: (Recursive t, f ~ Base t, Functor (Base t)) => Setter t (f a) t a
recursiveSetter = sets (. project) . mapped

corecursiveSetter :: forall t f a.
  (Corecursive t, f ~ Base t, Functor (Base t)) => Setter (f a) t a t
corecursiveSetter = sets (embed .) . mapped

recursiveTraversal
  :: (Recursive t, f ~ Base t, Traversable (Base t)) => Traversal t (f a) t a
recursiveTraversal eval f = traverse eval $ project f

corecursiveTraversal
  :: (Corecursive t, f ~ Base t, Traversable (Base t)) => Traversal (f a) t a t
corecursiveTraversal eval f = embed <$> traverse eval f

cataRecursive :: (Recursive t, f ~ Base t, Functor f) => (f a -> a) -> t -> a
cataRecursive alg = cata recursiveSetter %~ alg

anaCorecursive :: (Corecursive t, f ~ Base t, Functor f) => (a -> f a) -> a -> t
anaCorecursive coalg = ana corecursiveSetter %~ coalg

cataScanFn :: Functor f => (f a -> a) -> Array Int (f Int) -> Array Int a
cataScanFn alg = cataScan mapped %~ alg

hyloFunctorScan :: Functor f => (f b -> b) -> (a -> f Int) -> Array Int a -> Array Int b
hyloFunctorScan alg coalg = recurScan mapped %~ \(f, a) -> alg $ f $ coalg a

hyloFunctor :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hyloFunctor alg coalg = recur mapped %~ \(f, a) -> alg $ f $ coalg a

hyloT :: (Traversable f, Monad m) => (f b -> m b) -> (a -> m (f a)) -> a -> m b
hyloT alg coalg = traverseOf (recurT traversed)$ \(fa2fb, a) ->
  coalg a >>= fa2fb >>= alg

cocoRecursive
  :: (Recursive t, Functor g, f ~ Base t, h ~ Base u, Corecursive u)
  => (g (f t) -> h (g t)) -> g t -> u
cocoRecursive coalg = consuRecursive coalg embed

consuRecursive
  :: (Recursive t, Functor g, f ~ Base t, Functor h)
  => (g (f t) -> h (g t)) -> (h a -> a) -> g t -> a
consuRecursive coalg alg = hyloFunctor alg (coalg . fmap project)

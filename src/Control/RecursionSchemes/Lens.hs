{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Control.RecursionSchemes.Lens where

import Data.Functor.Compose
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
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

{-# INLINABLE recursion #-}
recursion :: Setter t a t a -> t -> a
recursion setter = rec where rec = setter %~ rec

{-# INLINABLE hylo #-}
hylo :: Setter ta tb a b -> Setter a b a (ta, tb -> b)
hylo setter = sets$ \eval ->
  let rec = eval >>> first (setter %~ rec) >>> uncurry (&) in rec

{-# INLINABLE cata #-}
cata :: Setter tt ta tt a -> Setter tt a ta a
cata setter = hylo setter . sets (\alg a -> (a, alg))

{-# INLINABLE ana #-}
ana :: Setter ta tt a tt -> Setter a tt a ta
ana setter = hylo setter . sets (\coalg a -> (coalg a, id))

{-# INLINABLE hyloT #-}
hyloT :: forall m ta tb a b. Monad m =>
  LensLike m ta tb a b -> LensLike m a b a (ta, tb -> m b)
hyloT setter eval = rec where
  rec a = do
    (ta, tb2b) <- eval a
    tb2b =<< traverseOf setter rec ta

{-# INLINABLE cataT #-}
cataT :: Monad m => LensLike m tt ta tt a -> LensLike m tt a ta a
cataT setter alg = rec where rec = setter rec >=> alg
  -- equivalent to: hyloT setter . \alg tt -> return (tt, alg)

{-# INLINABLE anaT #-}
anaT :: Monad m => LensLike m ta tt a tt -> LensLike m a tt a ta
anaT setter coalg = rec where rec = coalg >=> setter rec
  -- equivalent to: hyloT setter . \coalg ta -> coalg ta <&> (, return)

-- Ixed recursion

{-# INLINABLE hyloScan #-}
hyloScan ::
  ( Functor f
  , Ixed (f a)
  , Ixed (f b)
  , i ~ Index (f a)
  , i ~ Index (f b)
  , a ~ IxValue (f a)
  , b ~ IxValue (f b)
  )
  => Setter ti tb i b -> Setter (f a) (f b) a (ti, tb -> b)
hyloScan setter = sets$ \eval arr ->
  let arr' = fmap (eval >>> first (setter %~ \i -> arr' ^?! ix i) >>> uncurry (&)) arr
  in arr'

{-# INLINABLE cataScan #-}
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
cataScan setter = hyloScan setter . sets (\alg a -> (a, alg))

{-# INLINABLE anaScan #-}
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
anaScan setter = hyloScan setter . sets (\coalg a -> (coalg a, id))

-- MArray double bottom-up recursion (the first scan is actually a fmap a -> ti)

{-# INLINABLE hyloScanT #-}
hyloScanT :: forall arr i m ti tb a b.
  (Monad m, MArray arr b m, Ix i)
  => LensLike m ti tb i b
  -> LensLike m (Array i a) (arr i b) a (ti, tb -> m b)
hyloScanT setter eval as = do
  let bnds = bounds as
  bs <- newArray_ bnds
  forM_ (assocs as)$ \(i, a) -> do
    b <- do
      (ti, tb2b) <- eval a
      tb <- traverseOf setter (readArray bs) ti
      tb2b tb
    writeArray bs i b
  return bs

{-# INLINABLE cataScanT #-}
cataScanT :: forall arr m ti ta i a.
  (Monad m, MArray arr a m, Ix i)
  => LensLike m ti ta i a
  -> LensLike m (Array i ti) (arr i a) ta a
cataScanT setter = hyloScanT setter . \alg ti -> return (ti, alg)

{-# INLINABLE cataScanT' #-}
cataScanT' :: forall arr m ti ta i a.
  (Monad m, MArray arr a m, Ix i)
  => LensLike m ti ta i a
  -> LensLike m (Array i ti) (Array i a) ta a
cataScanT' setter alg arr0 = do
  arr <- hyloScanT @arr setter (\ti -> return (ti, alg)) arr0
  unsafeFreeze arr

{-# INLINABLE anaScanT #-}
anaScanT ::
  (Monad m, MArray arr t m, Ix i)
  => LensLike m ta t i t
  -> LensLike m (Array i a) (arr i t) a ta
anaScanT setter = hyloScanT setter . \coalg a -> coalg a <&> (, return)

-- MArray top-down ana

{-# INLINABLE anaScanT2List #-}
anaScanT2List :: forall mt i g tgi arr m tgi'.
  (MonadTrans mt, Monad (mt m), Ix i, Semigroup g, MArray arr g m)
  => LensLike m tgi tgi' (g, i) (g, i)
  -> LensLike (mt m) (arr i g) [tgi'] g tgi
anaScanT2List setter eval gs = do
  bnds <- lift$ getBounds gs
  (reverse <$>) . forM (reverse$ range bnds)$ \i -> do
    g <- lift$ readArray gs i
    tgi <- eval g
    lift$ flip (traverseOf setter) tgi$ \(gj, j) -> do
      gj0 <- readArray gs j
      let gj' = gj0 <> gj
      writeArray gs j gj'
      return (gj', j)

-- MArray top-down-bottom-up hylo

data Enclosing m1 m2 a = Enclosing (m1 ()) (m2 a)
instance Functor m2 => Functor (Enclosing m1 m2) where
  {-# INLINABLE fmap #-}
  fmap fn (Enclosing before after) = Enclosing before (fn <$> after)
instance (Applicative m1, Applicative m2) => Applicative (Enclosing m1 m2) where
  {-# INLINABLE pure #-}
  pure x = Enclosing (pure ()) (pure x)
  Enclosing bef1 fab <*> Enclosing bef2 fa =
    Enclosing (bef2 *> bef1) (fab <*> fa)

{-# INLINABLE simpleEncloser #-}
simpleEncloser ::
  (Ix i, Semigroup g, MArray arr' b m, MArray arr g m)
  => LensLike (Enclosing m (ReaderT (arr' i b) m)) tgi tb (g, i) b
  -> arr i g
  -> tgi
  -> Enclosing m (ReaderT (arr' i b) m) tb
simpleEncloser setter gs = traverseOf setter (arrayEncloser gs id)

{-# INLINABLE arrayEncloser #-}
arrayEncloser ::
  (Ix i, Semigroup g, MArray arr' b m, MArray arr g m)
  => arr i g
  -> (e -> arr' i b)
  -> (g, i)
  -> Enclosing m (ReaderT e m) b
arrayEncloser !gs !getBs (!g, !j) = Enclosing
  (readArray gs j >>= \g0 -> let !g1 = g0 <> g in writeArray gs j g1)
  (asks getBs >>= \bs -> lift$ readArray bs j)

{-# INLINABLE arrayEncloser' #-}
arrayEncloser' ::
  (Ix i, Semigroup g, MArray arr g m)
  => arr i g
  -> (e -> Array i b)
  -> (g, i)
  -> Enclosing m (ReaderT e m) b
arrayEncloser' !gs !getBs (!g, !j) = Enclosing
  (readArray gs j >>= \g0 -> let !g1 = g0 <> g in writeArray gs j g1)
  (asks getBs <&> (!j))

class Encloser e m1 m2 a | e -> m1 m2 a where
  actionBefore :: e -> m1 ()
  actionAfter :: e -> m2 a

instance Encloser (Enclosing m1 m2 a) m1 m2 a where
  actionBefore (Enclosing bef _) = bef
  actionAfter (Enclosing _ aft) = aft

{-# INLINABLE hyloScanT00 #-}
hyloScanT00 :: forall i g tgi arr arr' m tb b cs env encl.
  (Ix i, MArray arr g m, MArray arr' b m, Encloser encl m (ReaderT env m) tb)
  => m cs
  -> (arr' i b -> cs -> env)
  -> (tgi -> encl)
  -> LensLike m (arr i g) (cs, arr' i b) (g, i) (tgi, tb -> m b)
hyloScanT00 atTheBottom mkenv encloser eval gs = do
  bnds <- getBounds gs
  bs <- newArray_ bnds

  let
    step :: [i] -> m cs -> m cs
    step [] previousStep = previousStep
    step ((!i):rest) previousStep = do
      step rest$ do
        g <- readArray gs i
        (tgi, tb2b) <- eval (g, i)
        let encl = encloser tgi
        actionBefore encl
        cs <- previousStep
        tb <- runReaderT (actionAfter encl)$ mkenv bs cs
        b <- tb2b tb
        writeArray bs i b
        return cs

  (, bs) <$> step (range bnds) atTheBottom

{-# INLINABLE hyloScanT00' #-}
hyloScanT00' :: forall i g tgi arr m tb b cs env encl.
  (Ix i, MArray arr g m, MArray arr b m, Encloser encl m (ReaderT env m) tb)
  => m cs
  -> (arr i b -> cs -> env)
  -> (tgi -> encl)
  -> LensLike m (arr i g) (cs, arr i b) (g, i) (tgi, tb -> m b)
hyloScanT00' = hyloScanT00

{-# INLINABLE hyloScanTTerminal #-}
hyloScanTTerminal :: forall i g tgi arr arr' m tb b.
  (Ix i, Semigroup g, MArray arr g m, MArray arr' b m)
  => LensLike (Enclosing m (ReaderT (arr' i b) m)) tgi tb (g, i) b
  -> LensLike m (arr i g) (arr' i b) (g, i) (tgi, tb -> m b)
hyloScanTTerminal setter eval gs =
  snd <$> hyloScanT00 (return ()) const (simpleEncloser setter gs) eval gs

{-# INLINABLE hyloScanTTerminal' #-}
hyloScanTTerminal' :: forall i g tgi arr m tb b.
  (Ix i, Semigroup g, MArray arr g m, MArray arr b m)
  => LensLike (Enclosing m (ReaderT (arr i b) m)) tgi tb (g, i) b
  -> LensLike m (arr i g) (arr i b) (g, i) (tgi, tb -> m b)
hyloScanTTerminal' setter eval gs =
  snd <$> hyloScanT00 (return ()) const (simpleEncloser setter gs) eval gs

newtype Keep a = Keep {unKeep :: a}
instance Semigroup (Keep a) where
  {-# INLINABLE (<>) #-}
  x <> _ = x

-- Semantically equivalent to cataScanT but a bit more complex to implement
-- via hyloScanT2 as we need to make some dummy operations for types to fit.
{-# INLINABLE cataScanT2 #-}
cataScanT2 :: forall i ti arr arr' m ta a.
  ( Ix i
  , MArray arr ti m
  , MArray arr (Keep ti) m
  , MArray arr' a m
  )
  => Traversal ti ta i a
  -> LensLike m (arr i ti) (arr' i a) ta a
cataScanT2 setter alg arr = do
  let setter' ktii2a = setter (ktii2a . (undefined,))
  let hyloAlg (Keep ti, _) = return (ti, alg)
  (arr' :: Array i ti) <- unsafeFreeze arr  -- noop
  (arr'' :: arr i (Keep ti)) <- unsafeThaw$ fmap Keep arr'  -- noop
  hyloScanTTerminal setter' hyloAlg arr''

{-# INLINABLE anaScanT2 #-}
anaScanT2 ::
  (Ix i, Monoid g, MArray arr g m, MArray arr' t m)
  => LensLike (Enclosing m (ReaderT (arr' i t) m)) tgi t (g, i) t
  -> LensLike m (arr i g) (arr' i t) (g, i) tgi
anaScanT2 setter = hyloScanTTerminal setter . \coalg a -> coalg a <&> (, return)


-- Graph traversals: DFS --------------------------------------------------------------

{-# INLINABLE dfs #-}
dfs :: forall m g i arr g'.
  (Monad m, MArray arr g m, Ix i, Semigroup g)
  => LensLike m (g, i) g' (g, i) g'
  -> arr i g
  -> i
  -> m g'
dfs setter arr i = readArray arr i >>= rec . (, i) where
  rec (g, i) = flip setter (g, i)$ \(h, j) -> do
    child <- readArray arr j
    rec (child <> h, j)

-- Specialization for the recursion-schemes (and other) library compatibility

{-# INLINABLE recursiveSetter #-}
recursiveSetter :: (Recursive t, f ~ Base t, Functor (Base t)) => Setter t (f a) t a
recursiveSetter = sets (. project) . mapped

{-# INLINABLE corecursiveSetter #-}
corecursiveSetter :: forall t f a.
  (Corecursive t, f ~ Base t, Functor (Base t)) => Setter (f a) t a t
corecursiveSetter = sets (embed .) . mapped

{-# INLINABLE recursiveTraversal #-}
recursiveTraversal
  :: (Recursive t, f ~ Base t, Traversable (Base t)) => Traversal t (f a) t a
recursiveTraversal eval f = traverse eval $ project f

{-# INLINABLE corecursiveTraversal #-}
corecursiveTraversal
  :: (Corecursive t, f ~ Base t, Traversable (Base t)) => Traversal (f a) t a t
corecursiveTraversal eval f = embed <$> traverse eval f

{-# INLINABLE cataRecursive #-}
cataRecursive :: (Recursive t, f ~ Base t, Functor f) => (f a -> a) -> t -> a
cataRecursive alg = cata recursiveSetter %~ alg

{-# INLINABLE anaCorecursive #-}
anaCorecursive :: (Corecursive t, f ~ Base t, Functor f) => (a -> f a) -> a -> t
anaCorecursive coalg = ana corecursiveSetter %~ coalg

{-# INLINABLE cataScanFn #-}
cataScanFn :: Functor f => (f a -> a) -> Array Int (f Int) -> Array Int a
cataScanFn alg = cataScan mapped %~ alg

{-# INLINABLE hyloFunctorScan #-}
hyloFunctorScan :: Functor f => (f b -> b) -> (a -> f Int) -> Array Int a -> Array Int b
hyloFunctorScan alg coalg = hyloScan mapped %~ \a -> (coalg a, alg)

{-# INLINABLE hyloFunctor #-}
hyloFunctor :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hyloFunctor alg coalg = hylo mapped %~ \a -> (coalg a, alg)

{-# INLINABLE hyloTraversable #-}
hyloTraversable ::
  (Traversable f, Monad m)
  => (f b -> m b) -> (a -> m (f a)) -> a -> m b
hyloTraversable alg coalg = traverseOf (hyloT traversed)$ \a -> coalg a <&> (, alg)

{-# INLINABLE cocoRecursive #-}
cocoRecursive
  :: (Recursive t, Functor g, f ~ Base t, h ~ Base u, Corecursive u)
  => (g (f t) -> h (g t)) -> g t -> u
cocoRecursive coalg = consuRecursive coalg embed

{-# INLINABLE consuRecursive #-}
consuRecursive
  :: (Recursive t, Functor g, f ~ Base t, Functor h)
  => (g (f t) -> h (g t)) -> (h a -> a) -> g t -> a
consuRecursive coalg alg = hyloFunctor alg (coalg . fmap project)

-- Miscellaneous

{-# INLINABLE sideCata #-}
sideCata
  :: ASetter t1 t1' t2 a
  -> ASetter t1' a t1 a
  -> Setter t1 a t2 a
sideCata t1t2 t1t1 = sets$ \eval -> let rec = t1t2 %~ eval >>> t1t1 %~ rec in rec

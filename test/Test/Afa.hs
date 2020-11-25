{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}

module Test.Afa where

import Control.Monad.Reader
import Control.Monad.Identity
import Control.Lens
import Data.Monoid
import Control.Monad.ST
import Data.Array
import Data.Array.MArray
import Data.Array.ST
import Data.Traversable
import Data.Functor.Classes

import Test.Afa.Term (Term)
import Test.Afa.BoolP (BoolP)
import qualified Test.Afa.Term as T
import qualified Test.Afa.BoolP as P
import Control.RecursionSchemes.Lens
  ( simpleEncloser
  , arrayEncloser
  , Enclosing(..)
  , hyloScanT00'
  , runNoConsT
  , nocons
  )

newtype Tree f i = Tree (Either i (f (Tree f i)))
pattern Node x = Tree (Right x)
pattern Leaf i = Tree (Left i)

instance (Eq i, Eq1 f) => Eq (Tree f i) where
  Leaf a == Leaf b = a == b
  Node a == Node b = eq1 a b

instance (Show i, Show1 f) => Show (Tree f i) where
  showsPrec d (Leaf a) = showParen (d >= 11)$ showString "Leaf " . showsPrec 11 a 
  showsPrec d (Node a) = showParen (d >= 11)$ showString "Node " . showsPrec1 11 a 

treeModChilds :: Functor m
  => (i -> m j)
  -> LensLike m (f (Tree f i)) (g (Tree g j)) (Tree f i) (Tree g j)
  -> Tree f i
  -> m (Tree g j)
treeModChilds lLeaf setter = rec where
  rec (Leaf i) = Leaf <$> lLeaf i
  rec (Node x) = Node <$> setter rec x

instance Traversable f => Functor (Tree f) where fmap = fmapDefault
instance Traversable f => Foldable (Tree f) where foldMap = foldMapDefault
instance Traversable f => Traversable (Tree f) where
  traverse fn = treeModChilds fn traverse

qs :: [Int]
qs = [1, 3]

ts :: Array Int (Tree (Term Int Int) Int)
ts = listArray (0, 4)
  [ {- 0 -} Node$T.And [Node$T.P 2, Node T.LTrue]
  , {- 1 -} Node$T.Or [Leaf 0, Leaf 0, Node$T.Q 0]
  , {- 2 -} Node$T.And [Node$T.P 0, Node$T.P 1]
  , {- 3 -} Node$T.P 2
  , {- 4 -} Node$T.And [Leaf 2, Leaf 3, Node$T.P 0]
  ]

ps :: Array Int (Tree BoolP Int)
ps = listArray (0, 2)
  [ Node$P.Var 0
  , Node$P.And [Node$P.Var 1, Node$P.Var 2]
  , Node$P.Or [Node$P.And [Node$P.Var 1, Leaf 1], Leaf 1]
  ]

ts0 :: Array Int (Term Int Int Int)
ts0 = listArray (0, 4)
  [ T.LTrue
  , T.Or [0, 0]
  , T.P 0
  , T.P 2
  , T.P 0
  ]

ps0 :: Array Int (BoolP Int)
ps0 = listArray (0, 4)
  [ P.Var 0
  , P.Var 1
  , P.And [1, 1]
  ]

toArr :: [x] -> Array Int x
toArr xs = listArray (0, length xs - 1) xs

removeOrphans :: forall s. ST s
  ( [Int]
  , Array Int (Term Int Int Int)
  , Array Int (BoolP Int)
  )
removeOrphans = do
  (pReach :: STArray s Int Any) <- newArray (bounds ps) (Any False)
  (tReach :: STArray s Int Any) <- newArray (bounds ts) (Any False)
  let Enclosing qBefore qAfter = simpleEncloser traversed id tReach$ map (Any True,) qs
  runIdentityT qBefore

  let pScan = runNoConsT$ hyloScanT00'
        (return ()) (simpleEncloser traversed snd pReach) pHylogebra pReach

  (((_, psList), tsMapping), tsList) <-
    runNoConsT$ hyloScanT00'
      ( lift pScan )
      ( T.modChilds T.pureChildMod
          { T.lT = arrayEncloser tReach snd
          , T.lP = arrayEncloser pReach (snd . fst . fst)
          }
      )
      tHylogebra
      tReach

  qs' <- runIdentityT$ runReaderT qAfter tsMapping
  return (qs', toArr tsList, toArr psList)

  where
  noconsIf (Any False) _ = return (error "unreachable")
  noconsIf _ tb = nocons tb

  tHylogebra (g, i) = return$ (, noconsIf g)$ runIdentity$
    T.modChilds T.pureChildMod{ T.lT = return . (g,), T.lP = return . (g,) } (ts0!i)

  pHylogebra (g, i) = return$ ((g,) <$> ps0!i, noconsIf g)

removeOrphans' :: forall s. ST s
  ( [Int]
  , Array Int (Tree (Term Int Int) Int)
  , Array Int (Tree BoolP Int)
  )
removeOrphans' = do
  (pReach :: STArray s Int Any) <- newArray (bounds ps) (Any False)
  (tReach :: STArray s Int Any) <- newArray (bounds ts) (Any False)
  let Enclosing qBefore qAfter = simpleEncloser traversed id tReach$ map (Any True,) qs
  runIdentityT qBefore

  let pScan = runNoConsT$ hyloScanT00'
        (return ())
        (simpleEncloser traversed snd pReach)
        pHylogebra
        pReach

  (((_, psList), tsMapping), tsList) <-
    runNoConsT$ hyloScanT00'
      ( lift pScan )
      ( treeModChilds (arrayEncloser tReach snd)$ \rec ->
          T.modChilds T.pureChildMod
            { T.lT = rec
            , T.lP = arrayEncloser pReach (snd . fst . fst)
            }
      )
      tHylogebra
      tReach

  qs' <- runIdentityT$ runReaderT qAfter tsMapping
  return (qs', toArr tsList, toArr psList)

  where
  noconsIf (Any False) _ = return (error "unreachable")
  noconsIf _ tb = nocons tb

  tHylogebra (g, i) = return$ (, noconsIf g)$ runIdentity$ ($ ts!i)$
    treeModChilds (return . (g,))$ \rec ->
      T.modChilds T.pureChildMod{ T.lT = rec, T.lP = return . (g,) }

  pHylogebra (g, i) = return$ ((g,) <$> ps!i, noconsIf g)

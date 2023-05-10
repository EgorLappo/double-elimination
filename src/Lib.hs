{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Lib where

import qualified Data.Text                  as T
import qualified Data.Text.IO               as T

import           Control.Monad.State.Strict
import           Data.IntMap.Strict         (IntMap, (!))
import           Data.List                  (intercalate, tails)

import qualified Data.Array                 as A
import qualified Data.IntMap.Strict         as IMap
import qualified Data.IntSet                as ISet

data Node a
  = T a Int Int   -- label, left child index, right child index
  | H a Int      -- label, child index
  | L a          -- label
    deriving (Show, Eq)

instance Functor Node where
  fmap f (T a l r) = T (f a) l r
  fmap f (H a c)   = H (f a) c
  fmap f (L a)     = L (f a)

-- an adjacency list encoding of a rooted phylogenetic network
type RPN a = IntMap (Node a)

type UNode = Node ()
type URPN = RPN ()

mkDoubleEliminationU :: URPN -> URPN
mkDoubleEliminationU t
  | not (tree t) = error "mkDoubleElimination: input is not a tree"
  | otherwise = IMap.insert i (T () h lg) res
  where 
      ((h,lg), (i,res)) = runState(go (root t)) (0, IMap.empty)

      -- go returns two numbers given a pointer to a subtree
      -- the first is the pointer to the "hybridization node" that represents the winner (of the winners bracket) of the subtree
      -- the second is the pointer to the winner of the losers bracket of the subtree 
      go node = case t ! node of 
          T _ l r -> case (t ! l, t ! r) of
            (L _, L _) -> do 
              (n, net) <- get 
              let net' =  IMap.union net $ IMap.fromList [(n, L ()), (n+1, L ()), (n+2, T () n (n+1)), (n+3, H () (n+2))]
              put (n+4, net')
              return (n+3,n+3)
            (L _, T {}) -> do 
              (rh, rlg) <- go r
              (n, net) <- get
              let net' = IMap.union net $ IMap.fromList [(n, L ()), (n+1, T () n rh), (n+2, H () (n+1)), (n+3, T () (n+2) rlg)]
              put (n+4, net')
              return (n+2,n+3) -- node (n+1) is the game to determine the winner for the subtree and (n+3) is the winner of the losers bracket for the subtree
            (T {}, L _) -> do 
              (lh, llg) <- go r
              (n, net) <- get
              let net' = IMap.union net $ IMap.fromList [(n, L ()), (n+1, T () n lh), (n+2, H () (n+1)), (n+3, T () (n+2) llg)]
              put (n+4, net')
              return (n+2,n+3) -- node (n+1) is the game to determine the winner for the subtree and (n+3) is the winner of the losers bracket for the subtree
            (T {}, T {}) -> do
              (lh,llg) <- go l
              (rh,rlg) <- go r
              (n, net) <- get
              let net' = IMap.union net $ IMap.fromList [(n, T () lh rh), (n+1, T () llg rlg), (n+2, H () n), (n+3, T () (n+2) (n+1))]
              put (n+4, net')
              return (n+2,n+3) -- node n is the game between winners for subtrees, node (n+1) is the game among losers for each subtree, and node (n+3) is the winner of the losers bracket for the subtree
          _ -> error "mkDoubleElimination: unreachable!"


balancedTree :: Int -> URPN
balancedTree n = balancedTreeList n !! (n-1)

balancedTreeList :: Int -> [URPN]
balancedTreeList nmax =
  let ts = [balancedTreeMemo ts n | n <- [1..nmax]] in ts

balancedTreeMemo :: [URPN] -> Int -> URPN
balancedTreeMemo ts n 
  | n < 0 = error "balancedTree: n must be non-negative"
  | n == 0 = IMap.empty
  | n == 1 = IMap.fromList [(1, L ())]
  | n == 2 = IMap.fromList [(1, L ()),(2, L ()),(3, T () 1 2)]
  | otherwise = IMap.insert (2*m + 1) (T () m (2*m)) $ IMap.union t (incrementLabelsBy m t) 
  where 
    t = ts !! (n-2) 
    m = length $ labels t
    incrementLabelsBy i = fmap (idxmap (+i)) . IMap.mapKeys (+i)

    idxmap f (T a l r) = T a (f l) (f r)
    idxmap f (H a c)   = H a (f c)
    idxmap _ (L a)     = L a

-- ******** GENERATE TREE TOPOLOGIES ********
treeTopologies :: Int -> [URPN]
treeTopologies n = unlabeledTreesList n !! (n-1)

unlabeledTreesList :: Int -> [[URPN]]
unlabeledTreesList nmax =
  let ts = [unlabeledTreesMemo ts n | n <- [1..nmax]] in ts

unlabeledTreesMemo :: [[URPN]] -> Int -> [URPN]
unlabeledTreesMemo ts n
  | n < 0 = error "unlabeledTrees: n must be non-negative"
  | n == 0 = [IMap.empty]
  | n == 1 = [IMap.fromList [(1, L ())]]
  | n == 2 = [IMap.fromList [(1, L ()),(2, L ()),(3, T () 1 2)]]
  | n == 3 = [IMap.fromList [(1, L ()),(2, L ()),(3, L ()),(4, T () 2 3),(5, T () 1 4)]]
  | even n =
      let
        i = (n - 2) `div` 2
        unbalancedTrees = do
          k <- [1..i]
          l <- ts !! (k-1)
          r <- ts !! (n-k-1)
          return $ IMap.insert (2*n-1) (T () (2*k-1) (2*n-2)) $ IMap.union l (incrementLabelsBy (2*k - 1) r)

        halfTrees = ts !! ((n `div` 2) - 1)
        balancedTrees = do
          (l, r) <- pairs halfTrees
          return $ IMap.insert (2*n-1) (T () (2*(n `div` 2)-1) (2*n-2)) $ IMap.union l (incrementLabelsBy (2*(n `div` 2)-1) r)
      in unbalancedTrees ++ balancedTrees
  | otherwise =
      let
        i = (n - 1) `div` 2
      in do
        k <- [1..i]
        l <- ts !! (k-1)
        r <- ts !! (n-k-1)
        return $ IMap.insert (2*n-1) (T () (2*k-1) (2*n-2)) $ IMap.union l (incrementLabelsBy (2*k - 1) r)

  where incrementLabelsBy i = fmap (idxmap (+i)) . IMap.mapKeys (+i)

        pairs l = zip l l ++ [(x,y) | (x:ys) <- tails l, y <- ys]

        idxmap f (T a l r) = T a (f l) (f r)
        idxmap f (H a c)   = H a (f c)
        idxmap _ (L a)     = L a


-- ******** HELPERS ********
labelMap :: (a -> b) -> RPN a -> RPN b
labelMap f = fmap (fmap f)

reindexTree :: RPN a -> RPN a
reindexTree t
  | not (tree t) = error "relabelTree: input is not a tree"
  | otherwise = snd $ execState (go t (root t)) (0, IMap.empty)
  where go t' i = case t' ! i of
          L a -> do
            (n, m) <- get
            put (n+1, IMap.insert n (L a) m)
            return n
          T a l r -> do
            n1 <- go t' l
            n2 <- go t' r
            (n, m) <- get
            put (n+1, IMap.insert n (T a n1 n2) m)
            return n
          _ -> error "relabelTree: unreachable"

tree :: RPN a -> Bool
tree = all
  (\case
    T {} -> True
    L _     -> True
    _            -> False)

root :: RPN a -> Int
root d = head $ filter (isRoot d) (labels d)

labels :: RPN a -> [Int]
labels = IMap.keys

isRoot :: RPN a -> Int -> Bool
isRoot d i = null $ parents d i

parents :: RPN a -> Int -> [Int]
parents d i = filter (\j -> isChild d j i) $ labels d

isChild :: RPN a -> Int -> Int -> Bool
isChild d i j = j `elem` children d i

children :: RPN a -> Int -> [Int]
children d i = case d ! i of
  T _ l r -> [l, r]
  H _ c   -> [c]
  L _     -> []

isLeaf :: RPN a -> Int -> Bool
isLeaf d i = case d ! i of
  L _ -> True
  _   -> False

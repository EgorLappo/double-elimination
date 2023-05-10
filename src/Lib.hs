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
import           Data.Maybe                 (fromJust)

import qualified Data.Array                 as A
import qualified Data.IntMap.Lazy         as IMap
import qualified Data.IntSet                as ISet
import System.Random


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

getUniformResult :: Double ->  Int -> Int -> (Int, Int)
getUniformResult r i j = 
  let
    (winner, loser) = if r >= 0.5 then (i, j) else (j, i)
  in (winner, loser)

getSigmoidResult :: [Double] -> Double -> Double -> Int -> Int -> (Int, Int)
getSigmoidResult xs r lambda i j = let
  -- xs are in (0,1), assumed random, sorted in ascending order
    distance = lambda * (xs !! (i-1) - xs !! (j-1))
    a = sigmoid distance >= r
  in if a then (i,j) else (j,i)

getEquidistantSigmoidResult :: Double -> Double -> Int -> Int -> (Int, Int)
getEquidistantSigmoidResult lambda r i j = let
    distance = lambda * fromIntegral (i - j)
    a = sigmoid distance >= r
  in if a then (i,j) else (j,i)

sigmoid :: Double -> Double
sigmoid x = 1.0 / (1.0 + exp (negate x))

runTournament :: [Double] -> (Double -> Int -> Int -> (Int, Int)) -> RPN (Maybe Int) -> RPN Int
runTournament xs f brak = let
  -- xs are in (0,1), assumed random
  -- net is the bracket such that the head of each label tells you which team is to play (i.e. who won)
  net = IMap.fromList [(i, go x i) | (i, x) <- zip (IMap.keys brak) xs]
  go x node = case brak ! node of
    L k -> L [fromJust k]
    T _ l r -> let
      lp = head $ getLabel net l
      rp = head $ getLabel net r
      (winner, loser) = f x lp rp
      in T [winner, loser] l r
    H _ c -> let
      players = getLabel net c
      [_,loser] = players
      in H [loser] c
  in fmap (fmap head) net


mkDoubleEliminationLL :: RPN (Maybe Int) -> RPN (Maybe Int)
mkDoubleEliminationLL t
  | not (tree t) = error "mkDoubleElimination: input is not a tree"
  | otherwise = IMap.insert i (T Nothing h lg') res
  where
      ((h,lg'), (i,res)) = runState (go (root t)) (0, IMap.empty)

      -- go returns two numbers given a pointer to a subtree
      -- the first is the pointer to the "hybridization node" that represents the winner (of the winners bracket) of the subtree
      -- the second is the pointer to the winner of the losers bracket of the subtree 
      go node = case t ! node of
          T _ l r -> case (t ! l, t ! r) of
            (L (Just k1), L (Just k2)) -> do
              (n, net) <- get
              let net' =  IMap.union net $ IMap.fromList [(n, L (Just k1)), (n+1, L (Just k2)), (n+2, T Nothing n (n+1)), (n+3, H Nothing (n+2))]
              put (n+4, net')
              return (n+2,n+3)
            (L (Just k1), T {}) -> do
              (rg, rlg) <- go r
              (n, net) <- get
              let net' = IMap.union net $ IMap.fromList [(n, L (Just k1)), (n+1, T Nothing n rg), (n+2, H Nothing (n+1)), (n+3, T Nothing (n+2) rlg)]
              put (n+4, net')
              return (n+1,n+3) -- node (n+1) is the game to determine the winner for the subtree and (n+3) is the winner of the losers bracket for the subtree
            (T {}, L (Just k2)) -> do
              (lg, llg) <- go l
              (n, net) <- get
              let net' = IMap.union net $ IMap.fromList [(n, L (Just k2)), (n+1, T Nothing n lg), (n+2, H Nothing (n+1)), (n+3, T Nothing (n+2) llg)]
              put (n+4, net')
              return (n+1,n+3) -- node (n+1) is the game to determine the winner for the subtree and (n+3) is the winner of the losers bracket for the subtree
            (T {}, T {}) -> do
              (lg,llg) <- go l
              (rg,rlg) <- go r
              (n, net) <- get
              let net' = IMap.union net $ IMap.fromList [(n, T Nothing lg rg), (n+1, T Nothing llg rlg), (n+2, H Nothing n), (n+3, T Nothing (n+2) (n+1))]
              put (n+4, net')
              return (n,n+3) -- node n is the game between winners for subtrees, node (n+1) is the game among losers for each subtree, and node (n+3) is the winner of the losers bracket for the subtree
          _ -> error "mkDoubleElimination: unreachable!"

mkDoubleEliminationU :: URPN -> URPN
mkDoubleEliminationU t
  | not (tree t) = error "mkDoubleElimination: input is not a tree"
  | otherwise = IMap.insert i (T () h lg) res
  where
      ((h,lg), (i,res)) = runState (go (root t)) (0, IMap.empty)

      -- go returns two numbers given a pointer to a subtree
      -- the first is the pointer to the "hybridization node" that represents the winner (of the winners bracket) of the subtree
      -- the second is the pointer to the winner of the losers bracket of the subtree 
      go node = case t ! node of
          T _ l r -> case (t ! l, t ! r) of
            (L _, L _) -> do
              (n, net) <- get
              let net' =  IMap.union net $ IMap.fromList [(n, L ()), (n+1, L ()), (n+2, T () n (n+1)), (n+3, H () (n+2))]
              put (n+4, net')
              return (n+2,n+3)
            (L _, T {}) -> do
              (rh, rlg) <- go r
              (n, net) <- get
              let net' = IMap.union net $ IMap.fromList [(n, L ()), (n+1, T () n rh), (n+2, H () (n+1)), (n+3, T () (n+2) rlg)]
              put (n+4, net')
              return (n+1,n+3) -- node (n+1) is the game to determine the winner for the subtree and (n+3) is the winner of the losers bracket for the subtree
            (T {}, L _) -> do
              (lh, llg) <- go r
              (n, net) <- get
              let net' = IMap.union net $ IMap.fromList [(n, L ()), (n+1, T () n lh), (n+2, H () (n+1)), (n+3, T () (n+2) llg)]
              put (n+4, net')
              return (n+1,n+3) -- node (n+1) is the game to determine the winner for the subtree and (n+3) is the winner of the losers bracket for the subtree
            (T {}, T {}) -> do
              (lh,llg) <- go l
              (rh,rlg) <- go r
              (n, net) <- get
              let net' = IMap.union net $ IMap.fromList [(n, T () lh rh), (n+1, T () llg rlg), (n+2, H () n), (n+3, T () (n+2) (n+1))]
              put (n+4, net')
              return (n,n+3) -- node n is the game between winners for subtrees, node (n+1) is the game among losers for each subtree, and node (n+3) is the winner of the losers bracket for the subtree
          _ -> error "mkDoubleElimination: unreachable!"

b4 :: RPN (Maybe Int)
b4 = IMap.fromList [(1,L (Just 1)),(2,L (Just 2)),(3,T Nothing 1 2),(4,L (Just 3)),(5,L (Just 4)),(6,T Nothing 4 5),(7,T Nothing 3 6),(8,L (Just 5)),(9,L (Just 6)),(10,T Nothing 8 9),(11,L (Just 7)),(12,L (Just 8)),(13,T Nothing 11 12),(14,T Nothing 10 13),(15,T Nothing 7 14)]

b3 :: RPN (Maybe Int)
b3 = IMap.fromList [(1,L (Just 1)),(2,L (Just 2)),(3,T Nothing 1 2),(4,L (Just 3)),(5,L (Just 4)),(6,T Nothing 4 5),(7,T Nothing 3 6)]

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

trees :: Int -> [URPN]
trees n = treesList n !! (n-1)

treesList :: Int -> [[URPN]]
treesList nmax =
  let ts = [treesMemo ts n | n <- [1..nmax]] in ts

treesMemo :: [[URPN]] -> Int -> [URPN]
treesMemo ts n
  | n < 0 = error "trees: n must be non-negative"
  | n == 0 = [IMap.empty]
  | n == 1 = [IMap.fromList [(1, L ())]]
  | otherwise = concatMap (\t -> insertAbove' t <$> labels t) $ ts !! (n-2)
  where
    insertAbove' t i
      | isRoot t i = IMap.union (IMap.fromList [(2*n-2, L ()), (2*n-1, T () i (2*n-2))]) t
      | otherwise =
        let p = head (parents t i)
            (T () l r) = t ! p
        in if l == i
              then IMap.union (IMap.fromList [(2*n-2, L ()), (2*n-1, T () i (2*n-2)), (p, T () (2*n-1) r)]) t
              else IMap.union (IMap.fromList [(2*n-2, L ()), (2*n-1, T () (2*n-2) i), (p, T () l (2*n-1))]) t

llTrees :: Int -> [RPN (Maybe Int)]
llTrees n = llTreesList n !! (n-1)

llTreesList :: Int -> [[RPN (Maybe Int)]]
llTreesList nmax =
  let ts = [llTreesMemo ts n | n <- [1..nmax]] in ts

llTreesMemo :: [[RPN (Maybe Int)]] -> Int -> [RPN (Maybe Int)]
llTreesMemo ts n
  | n < 0 = error "trees: n must be non-negative"
  | n == 0 = [IMap.empty]
  | n == 1 = [IMap.fromList [(1, L (Just 1))]]
  | otherwise = concatMap (\t -> insertAbove' t <$> labels t) $ ts !! (n-2)
  where
    insertAbove' t i
      | isRoot t i = IMap.union (IMap.fromList [(2*n-2, L (Just n)), (2*n-1, T Nothing i (2*n-2))]) t
      | otherwise =
        let p = head (parents t i)
            (T Nothing l r) = t ! p
        in if l == i
              then IMap.union (IMap.fromList [(2*n-2, L (Just n)), (2*n-1, T Nothing i (2*n-2)), (p, T Nothing (2*n-1) r)]) t
              else IMap.union (IMap.fromList [(2*n-2, L (Just n)), (2*n-1, T Nothing (2*n-2) i), (p, T Nothing l (2*n-1))]) t

isIsomorphic :: RPN a -> RPN b -> Bool
isIsomorphic net1 net2 = tryMatch net1 net2 (root net1) (root net2)

tryMatch :: RPN a -> RPN b -> Int -> Int -> Bool
tryMatch net1 net2 v1 v2
  | isLeaf net1 v1 && isLeaf net2 v2 = True
  | not $ sameNodeType (net1 ! v1) (net2 ! v2) = False
  | otherwise = case (net1 ! v1, net2 ! v2) of
    (T _ l1 r1, T _ l2 r2) -> tryMatch net1 net2 l1 l2 && tryMatch net1 net2 r1 r2 || tryMatch net1 net2 l1 r2 && tryMatch net1 net2 r1 l2
    (H _ i1, H _ i2) -> tryMatch net1 net2 i1 i2
  where sameNodeType (T {}) (T {}) = True
        sameNodeType (H _ _) (H _ _) = True
        sameNodeType (L _) (L _) = True
        sameNodeType _ _ = False
-- ******** HELPERS ********
pprintRPN :: Show a => RPN a -> IO ()
pprintRPN = mapM_ print . IMap.toList

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

getLabel :: RPN a -> Int -> a
getLabel d i = case d ! i of
  L a -> a
  T a _ _ -> a
  H a _ -> a

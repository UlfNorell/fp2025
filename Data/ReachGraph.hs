module Data.ReachGraph where

import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Maybe

type ReachGraph a = Map a (Set a)

addReachEdge :: Ord a => a -> a -> ReachGraph a -> ReachGraph a
addReachEdge x y g = addYs <$> (Map.insertWith (<>) x (Set.singleton y) g)
  where
    ys = Set.insert y $ fromMaybe mempty (Map.lookup y g)
    addYs zs
      | Set.member x zs = ys <> zs
      | Set.member y zs = ys <> zs
      | otherwise       = zs


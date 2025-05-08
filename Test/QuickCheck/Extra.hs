module Test.QuickCheck.Extra
  ( module Test.QuickCheck
  , module Test.QuickCheck.Extra
  ) where

import Text.Pretty
import Text.Printf
import Test.QuickCheck hiding (Result)

counterexampleP :: (Pretty a, Testable p) => a -> p -> Property
counterexampleP = counterexample . showP

counterexampleD :: Testable p => [Doc] -> p -> Property
counterexampleD = counterexample . show . vcat

-- Random list of positive integers summing to a given value.
genSum :: Int -> Gen [Int]
genSum n | n < 1 = error $ printf "genSum: %d < 1" n
genSum n = shuffle =<< go n
  where
    go 0 = pure []
    go n = choose (1, n) >>= \ k -> (k :) <$> go (n - k)


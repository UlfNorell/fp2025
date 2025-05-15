module Main where

import System.Environment
import Turing (bruteIO, bruteForce, bruteExplore, explore, Machine)
import Turing.Machine.Macro (exploreIO, toPrim, printStats)
import Text.Pretty

readArgs :: IO [Int]
readArgs = map read <$> getArgs

brute :: Int -> [Machine] -> IO ()
brute bound ms0 = () <$ bruteIO (bruteForce bound ms0)

main :: IO ()
main =
  readArgs >>= \ case
    [n, lo, bound]    ->
      () <$ bruteIO (bruteExplore $ explore n lo bound)
    [n, bound]    -> do
      ((_, m), stats) <- exploreIO n bound
      printStats stats
      print $ pPrint $ toPrim m
    _ -> putStrLn "Bad args"


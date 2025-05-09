module Main where

import System.Environment
import Turing (bruteIO, bruteForce, bruteExplore, explore, Machine)
import Turing.Machine.Macro (exploreIO)
import Text.Pretty

readArgs :: IO [Int]
readArgs = map read <$> getArgs

brute :: Int -> [Machine] -> IO ()
brute bound ms0 = () <$ bruteIO (bruteForce bound ms0)

main :: IO ()
main =
  readArgs >>= \ case
    -- [n, bound, a, b] -> brute bound $ take b $ drop a $ enum n
    -- [n, bound, a]    -> brute bound $ drop a $ enum n
    [n, lo, bound]    ->
      () <$ bruteIO (bruteExplore $ explore n lo bound)
    [n, bound]    -> do
      (_, m) <- exploreIO n bound
      print $ pPrint m
    _ -> putStrLn "Bad args"


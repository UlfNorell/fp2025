module Main where

import System.Environment
import Turing (bruteIO, bruteForce, bruteExplore, explore)

main :: IO ()
main = do
  let brute bound ms0 = () <$ bruteIO (bruteForce bound ms0)
  map read <$> getArgs >>= \ case
    -- [n, bound, a, b] -> brute bound $ take b $ drop a $ enum n
    -- [n, bound, a]    -> brute bound $ drop a $ enum n
    [n, lo, bound]    ->
      () <$ bruteIO (bruteExplore $ explore n lo bound)
    [n, bound]    ->
      () <$ bruteIO (bruteExplore $ explore n 0 bound)
    _ -> putStrLn "Bad args"
    -- [n] ->
    --   print $ length $ enum n
    -- [] -> do
    --   let go :: Int -> Int -> [Config] -> IO ()
    --       go _ _ [] = pure ()
    --       go !i !lo ((_, Tape n _ _) : confs)
    --         | mod i 1000000 == 0 = do
    --             printf "%8d: %6d (lo=%6d)\n" i n lo
    --             go (i + 1) maxBound confs
    --         | otherwise          =
    --             go (i + 1) (min lo n) confs
    --   go 1 maxBound $ traceRun bb5'


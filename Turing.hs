{-# LANGUAGE LambdaCase #-}
module Main where

import Control.Applicative
import Control.Monad
import Data.List
import Data.Ord
import Data.Set qualified as Set
import System.Environment
import Debug.Trace

------------------------------------------------------------------
-- a Symbol is what is written on the tape
-- a State is the value of the internal state of a machine

data Symbol = O | I deriving ( Eq, Ord )
data State  = A | B | C | D | E | F | H deriving ( Eq, Ord, Show, Enum )

instance Show Symbol where
  show O = "-"
  show I = "x"

------------------------------------------------------------------
-- a Tape is a pair of lists
-- the head is at the first element of the second list
-- the first list is reversed

type Tape = ([Symbol],[Symbol])

tape0 :: Tape
tape0 = ([], repeat O)

look :: Tape -> Symbol
look (_, x:_) = x

write :: Symbol -> Tape -> Tape
write x (ls, _:rs) = (ls, x:rs)

-- we can move (L)eft or (R)ight on a Tape

data Dir = L | R
  deriving ( Eq, Ord, Show )

move :: Dir -> Tape -> Tape
move L (  [],   rs) = (  [],   rs) -- bouncing
move L (x:ls,   rs) = (  ls, x:rs)
move R (  ls, x:rs) = (x:ls,   rs)

------------------------------------------------------------------
-- a Config is a pair of a state and a tape

type Config = (State,Tape)

-- a Rule describes what should happen if
-- we are in a given state and read a given symbol;
-- we get a new state, a new symbol, and a direction

data Rule = (State, Symbol) :-> (State, Symbol, Dir)
  deriving ( Eq, Ord, Show )

rule :: Rule -> Config -> Maybe Config
rule ((s0,x0) :-> (s1,x1,d)) (s, tape)
  | s0 == s && x0 == look tape = Just (s1, move d (write x1 tape))
  | otherwise                  = Nothing

rules :: [Rule] -> Config -> Maybe Config
rules rls conf = foldr (<|>) Nothing [ rule r conf | r <- rls ]

------------------------------------------------------------------
-- running a set of rules to completion

run :: [Rule] -> Int -> Config -> (Int, Config)
run rls n conf = n `seq` case rules rls conf of
                           Nothing    -> (n, conf)
                           Just conf' -> run rls (n+1) conf'

run' :: Int -> [Rule] -> Int -> Config -> Maybe (Int, Config)
run' 0 rls n conf = Nothing
run' fuel rls n conf = n `seq` case rules rls conf of
                           Nothing    -> Just (n, conf)
                           Just conf' -> run' (fuel - 1) rls (n+1) conf'

runTo :: Int -> Machine -> Maybe Int
runTo fuel m = fst <$> run' fuel m 0 (A, tape0)

vizrun :: Int -> [Rule] -> Int -> Config -> IO (Int, Config)
vizrun w rls n conf@(s, (ls, rs)) =
  n `seq`
  do putStrLn $ take w
       $ concat [ " " ++ show x ++ " " | x <- reverse ls ]
      ++ show s
      ++ concat [ show x ++ "  " | x <- rs ]
     case rules rls conf of
       Nothing    -> return (n, conf)
       Just conf' -> vizrun w rls (n+1) conf'

score :: [Rule] -> Int
score rs = fst (run rs 0 (A,tape0))

------------------------------------------------------------------

vrun :: Machine -> IO ()
vrun m = vizrun 80 m 0 (A, tape0) >>= print . fst

-- main :: IO ()
-- main = vrun example -- vizrun 80 example 0 (A,tape0) >>= print . fst

type Machine = [Rule]

byHand :: Machine
byHand = [ (A, O) :-> (A, I, L)
         , (A, I) :-> (B, I, R)
         , (B, O) :-> (B, I, L)
         , (B, I) :-> (H, O, L)
         ]

-- Score: 2
bb1 :: Machine
bb1 = [ (A, O) :-> (A, I, L)
      , (A, I) :-> (H, O, L)
      ]

-- Score: 10
bb2 :: Machine
bb2 = [ (A, O) :-> (B, I, L)
      , (A, I) :-> (H, O, L)
      , (B, O) :-> (A, I, L)
      , (B, I) :-> (B, O, R)
      ]

-- Score: 45
bb3 :: Machine
bb3 = [ (A,O) :-> (B,O,L)
      , (A,I) :-> (C,I,L)
      , (B,O) :-> (C,I,R)
      , (B,I) :-> (H,O,L)
      , (C,O) :-> (A,I,L)
      , (C,I) :-> (C,O,R) ]

example :: Machine
example = [ (A,O) :-> (B,I,R)
          , (A,I) :-> (B,O,R)
          , (B,O) :-> (C,O,R)
          , (B,I) :-> (H,O,R)
          , (C,O) :-> (C,I,L)
          , (C,I) :-> (A,I,R)
          ]

------------------------------------------------------------------

enum :: Int -> [Machine]
enum n = go False [A] (tail states) [] inputs
  where
    states = take n [A ..]
    inputs = [ (s, i) | s <- states, i <- [O, I] ]

    go halted old new acc [] = [reverse acc | halted]
    go halted old new acc ((s, i) : is) = do
      -- If we gotten to s and it's still new, it's won't be reachable!
      guard $ notElem s new
      -- At most one halting transition and only consider the first of the "new" states
      s' <- [ H | not halted ] ++ take 1 new ++ old
      o  <- [O, I]
      d  <- [L, R]
      when (s' == H) $ guard $ and [ o == O, d == L, (s, i) /= (A, O) ]
      let (old', new')
            | [s'] == take 1 new = (s' : old, drop 1 new)
            | otherwise          = (old, new)
          rule = (s, i) :-> (s', o, d)
      go (halted || s' == H) old' new' (rule : acc) is

bruteForce :: Int -> [Machine] -> [(Int, Machine)]
bruteForce bound ms = go 1 0 tms
  where
    tms = [ (n, m) | m <- ms, Just n <- [runTo bound m] ]
    go _ best [] = []
    go i best ((n, m) : tms)
      | n > best  = (n, m) : go' (i + 1) n tms
      | otherwise = go' (i + 1) best tms
    go' i best tms
      | mod i 10000000 == 0 = trace (show i) $ go i best tms
      | otherwise           = go i best tms

main :: IO ()
main =
  map read <$> getArgs >>= \ case
    [n, bound, a, b] ->
      mapM_ print $ bruteForce bound (take b $ drop a $ enum n)
    [n, bound] ->
      mapM_ print $ bruteForce bound (enum n)
    [n, a, b] ->
      print $ length $ take b $ drop a $ enum n
    [n] ->
      print $ length $ enum n


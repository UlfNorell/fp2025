{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import Control.Arrow (first)
import Control.Applicative
import Control.Monad
import Data.Bits
import Data.List
import Data.Ord
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import System.Environment
import Debug.Trace
import Data.Array.Unboxed
import Data.Array.Base (unsafeAt)
import Data.Word
import Data.Char
import Text.Printf

------------------------------------------------------------------
-- a Symbol is what is written on the tape
-- a State is the value of the internal state of a machine

data Symbol = O | I deriving ( Eq, Ord, Show, Enum )
data State  = A | B | C | D | E | F | H deriving ( Eq, Ord, Show, Enum )

-- instance Show Symbol where
--   show O = "-"
--   show I = "x"

------------------------------------------------------------------
-- a Tape is a pair of lists
-- the head is at the first element of the second list
-- the first list is reversed

type Tape = Tape' Symbol
data Tape' a = Tape {-# UNPACK #-} !Int [a] [a]
  deriving (Eq, Ord, Show)

tape0 :: Enum a => Tape' a
tape0 = Tape 0 [] []

look :: Tape -> Symbol
look (Tape _ _ [])    = O
look (Tape _ _ (x:_)) = x

write :: Symbol -> Tape -> Tape
write O (Tape n ls    [])  = Tape n ls    []
write I (Tape n ls    [])  = Tape n ls (I:[])
write O (Tape n ls (_:[])) = Tape n ls    []
write x (Tape n ls (_:rs)) = Tape n ls (x:rs)

-- we can move (L)eft or (R)ight on a Tape

data Dir = L | R
  deriving ( Eq, Ord, Show, Enum )

move :: Dir -> Tape -> Tape
move L (Tape n  []      rs)  = Tape 0       []        rs -- bouncing
move L (Tape n (O:ls)   [])  = Tape (n - 1) ls        []
move L (Tape n (x:ls)   rs)  = Tape (n - 1) ls     (x:rs)
move R (Tape n  ls   (x:rs)) = Tape (n + 1) (x:ls)    rs
move R (Tape n  ls      [])  = Tape (n + 1) (O:ls)    []

------------------------------------------------------------------
-- a Config is a pair of a state and a tape

type Config = (State, Tape)

-- a Rule describes what should happen if
-- we are in a given state and read a given symbol;
-- we get a new state, a new symbol, and a direction

data Rule = (State, Symbol) :-> (State, Symbol, Dir)
  deriving ( Eq, Ord, Show )

type Machine = [Rule]

rule :: Rule -> Config -> Maybe Config
rule ((s0,x0) :-> (s1,x1,d)) (s, tape)
  | s0 == s && x0 == look tape = Just (s1, move d (write x1 tape))
  | otherwise                  = Nothing

rules :: Machine -> Config -> Maybe Config
rules rls conf = foldr (<|>) Nothing [ rule r conf | r <- rls ]

-- Running a set of rules to completion -----------------------------------

initConf :: Config
initConf = (A, tape0)

run :: Machine -> Int -> Config -> (Int, Config)
run rls n conf = n `seq` case rules rls conf of
                           Nothing    -> (n, conf)
                           Just conf' -> run rls (n+1) conf'

vizrun :: Int -> Int -> Machine -> Int -> Config -> IO (Int, Config)
vizrun w 0 _ n conf = do
  putStrLn "Out of fuel!"
  pure (n, conf)
vizrun w fuel rls n conf@(s, Tape ln ls rs) =
  n `seq`
  do putStrLn
       $ printf "%4d " ln
      ++ concat [ " " ++ show x ++ " " | x <- take (div (w - 5) 3) $ reverse ls ]
      ++ "\ESC[31m" ++ show s ++ "\ESC[0m"
      ++ concat [ show x ++ "  " | x <- take (max 0 $ div (w - 5) 3 - ln) rs ]
     case rules rls conf of
       Nothing    -> return (n, conf)
       Just conf' -> vizrun w (fuel - 1) rls (n + 1) conf'

vrun :: Int -> Machine -> IO ()
vrun n m = vizrun 200 n m 0 initConf >>= print . fst

score :: Machine -> Int
score rs = fst (run rs 0 initConf)

-- Smarter running --------------------------------------------------------

data Reason = GiveUp | StuckLeft | RunAway | NoPath | Loop | TooWide
  deriving (Eq, Ord, Show)

data LoopAnalysis = LoopAnalysis
  { leftStuck    :: [(State, Symbol)]
  , noPathToHalt :: [(State, Symbol)]
  }
  deriving Show

loopAnalysis :: Machine -> LoopAnalysis
loopAnalysis m = LoopAnalysis
  { leftStuck    = goLeftStuck [ ((s1, i), (s2, o)) | (s1, i) :-> (s2, o, L) <- m, s2 /= H ]
  , noPathToHalt = goNoPath m
  }
  where
    goLeftStuck g
      | g == g'   = is
      | otherwise = goLeftStuck g'
      where
        is  = map fst g
        g'  = [ e | e@(_, o) <- g, elem o is ]

    goNoPath g
      | g == g'   = is
      | otherwise = goNoPath g'
      where
        is = [ i | i :-> _ <- g ]
        g' = [ e | e@(_ :-> (s, _, _)) <- g, elem (s, O) is && elem (s, I) is ]

unknown :: Int -> Int -> [Machine]
unknown fuel n = [ m | m <- enum n, Left GiveUp <- [runTo fuel m] ]

runUnknown fuel n i = m <$ vrun fuel m
  where
    m : _ = drop i $ unknown fuel n


loopCheck :: LoopAnalysis -> Int -> Config -> Config -> Maybe Reason
loopCheck loop _ _ (s, tape@(Tape _ [] _))
  | elem (s, look tape) (leftStuck loop) = Just StuckLeft
loopCheck loop _ (s1, Tape _ _ []) (s2, Tape _ _ [])
  | s1 == s2 = Just RunAway
loopCheck loop _ _ (s, tape)
  | elem (s, look tape) (noPathToHalt loop) = Just NoPath
loopCheck _ n _ (s, Tape w _ _)
  | n > 100, w * 6 > n = Just TooWide
loopCheck _ _ _ _ = Nothing

runToRef :: Int -> Machine -> Either Reason Int
runToRef fuel m = go fuel 0 (A, tape0)
  where
    go 0 n conf = Left GiveUp
    go fuel !n conf = case rules m conf of
      Nothing    -> Right n
      Just conf' -> go (fuel - 1) (n + 1) conf'

tapeSize :: Tape -> Int
tapeSize (Tape n ls rs) = n + length rs

runTo :: Int -> Machine -> Either Reason Int
runTo fuel = fst . runTo' () (\ _ _ -> id) fuel

runTo' :: s -> (Int -> Config -> s -> s) -> Int -> Machine -> (Either Reason Int, s)
runTo' s0 updS fuel m = go s0 fuel 0 mempty (A, tape0)
  where
    loop = loopAnalysis m
    go s 0 n seen conf = (Left GiveUp, s)
    go !s fuel !n seen conf@(_, tape)
      | shouldCache, Set.member conf seen = (Left Loop, s)
      | otherwise = case rules m conf of
          Nothing    -> (Right n, s)
          Just conf' ->
            case loopCheck loop n conf conf' of
              Just reason -> (Left reason, s)
              Nothing     -> go (updS n conf s) (fuel - 1) (n + 1) seen' conf'
      where
        shouldCache = n < 25 && sz <= 5
        sz = tapeSize tape
        seen' | shouldCache = Set.insert conf seen
              | otherwise   = seen

traceRun :: Machine -> [(State, Tape)]
traceRun m = go (A, tape0)
  where
    go conf =
      case rules m conf of
        Nothing    -> []
        Just conf' -> conf : go conf'

unvisited :: Int -> Machine -> Set (State, Symbol)
unvisited fuel m = Set.difference allStates visited
  where
    allStates = Set.fromList [ i | i :-> _ <- m ]
    visited = snd $ runTo' mempty (\ _ (s, tape) -> Set.insert (s, look tape)) fuel m

-- Compiled machines ------------------------------------------------------

-- For some reason this isn't faster!

type IMap = UArray Int Int
data Compiled = Compiled
  { nextStates :: IMap
  , writes     :: IMap
  , directions :: IMap
  }
  deriving Show

compile :: Machine -> Compiled
compile (sort -> rules) = Compiled
  { nextStates = mkIMap (\ (s, _, _) -> fromEnum s)
  , writes     = mkIMap (\ (_, o, _) -> fromEnum o)
  , directions = mkIMap (\ (_, _, d) -> fromEnum d)
  }
  where
    mkIMap f = listArray (0, length rules - 1) [ f o | _ :-> o <- rules ]

-- runC :: Int -> Machine -> Maybe Int
-- runC fuel m = go fuel 0 (fromEnum A) tape0
--   where
--     cm   = compile m
--     halt = fromEnum H

--     go :: Int -> Int -> Int -> Tape' Int -> Maybe Int
--     go 0 _ _ _ = Nothing
--     go fuel !n s tape
--       | s == halt = Just n
--       | otherwise = go (fuel - 1) (n + 1) s' tape'
--       where
--         i = look tape
--         ix = 2 * s + i
--         s' = nextStates cm `unsafeAt` ix
--         o  = writes cm     `unsafeAt` ix
--         d  = directions cm `unsafeAt` ix
--         tape' = move (toEnum d) (write o tape)

-- Skeletons --------------------------------------------------------------

data RuleSkeleton = (State, Symbol) :=> State
  deriving (Show, Eq, Ord)
type Skeleton = [RuleSkeleton]

-- Is the halting state reachable from state reachable?
hReachable :: Skeleton -> Bool
hReachable m = all (Set.member H) (reachability m)

reachability :: Skeleton -> Map State (Set State)
reachability m = go $ Map.unionsWith (<>) [ Map.singleton s (Set.singleton s1) | (s, _) :=> s1 <- m ]
  where
    go g | g == g'   = g
         | otherwise = go g'
      where
        g' = Map.unionsWith (<>) $ g : [ Map.singleton s (g Map.! s1)
                                       | (s, _) :=> s1 <- m, s1 /= H ]

-- Enumerating machines ---------------------------------------------------

-- Number of spines
--  n        no-opt      spines      H-reach
--  1             1           1            1
--  2            24          16           15
--  3         1,215         297          265
--  4       114,688       7,433        6,438
--  5    17,578,125     228,045      199,319
enumSkeletons :: Int -> [Skeleton]
enumSkeletons n = filter postChecks $ go False [A] (tail states) [] inputs
  where
    states = take n [A ..]
    inputs = [ (s, i) | s <- states, i <- [O, I] ]

    postChecks spine
      | not $ hReachable spine = False
      | otherwise              = True

    go halted old new acc [] = [reverse acc | halted]
    go halted old new acc ((s, i) : is) = do
      -- If we gotten to s and it's still new, it's won't be reachable!
      guard $ notElem s new
      -- At most one halting transition and only consider the first of the "new" states
      s' <- [ H | not halted ] ++ take 1 new ++ old
      when (s' == H) $ guard $ (s, i) /= (A, O)
      let (old', new')
            | [s'] == take 1 new = (s' : old, drop 1 new)
            | otherwise          = (old, new)
          rule = (s, i) :=> s'
      go (halted || s' == H) old' new' (rule : acc) is

fillSkeleton :: Skeleton -> [Machine]
fillSkeleton = go False []
  where
    go one acc [] = [ reverse acc | one ]
    go one acc (i :=> H : rs) = go one (i :-> (H, O, L) : acc) rs
    go !one acc (i :=> s' : rs) = do
      o <- [O, I]
      d <- [L, R]
      go (one || o == I) (i :-> (s', o, d) : acc) rs

-- Number of machines
--  n           old        spines       H-reach
--  1             4             2             2
--  2         1,024           896           840
--  3       304,128       294,624       262,880
--  4   120,324,096   119,384,064   104,656,128
--  5
enum :: Int -> [Machine]
enum = concatMap fillSkeleton . enumSkeletons

enum' :: Int -> [Machine]
enum' n = go False [A] (tail states) [] inputs
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

data Class = Terminated | NonTerminated Reason
  deriving (Eq, Ord, Show)
type Stats = Map Class Int

bruteForce :: Int -> [Machine] -> ([(Int, Int, Machine)], Stats)
bruteForce bound ms = go 1 0 ms mempty
  where
    go _ best [] stats = ([], stats)
    go i best (m : ms) !stats =
      case r of
        Left{} -> go' (i + 1) best ms stats'
        Right n
          | n > best  -> first ((n, i, m):) (go' (i + 1) n ms stats')
          | otherwise -> go' (i + 1) best ms stats'
      where
        r = runTo bound m
        s = case r of
              Right{} -> Terminated
              Left r  -> NonTerminated r
        stats' = Map.insertWith (+) s 1 stats
      -- case runTo bound m of

      -- | n > best  = (n, m) : go' (i + 1) n tms
      -- | otherwise = go' (i + 1) best tms
    go' i best tms stats
      | mod i 1000000 == 0 = trace (show i) $ go i best tms stats
      | otherwise          = go i best tms stats

main :: IO ()
main = do
  let brute bound ms0 = do
        let (ms, stats) = bruteForce bound ms0
        mapM_ print ms
        let why Terminated = "Terminated"
            why (NonTerminated r) = show r
            total = sum stats
        sequence_ [ printf "%-10s %9d  (%4.1f%%)\n" (why r) n (100 * fromIntegral @_ @Double n / fromIntegral total)
                  | (r, n) <- Map.toList stats ]
        printf "%-10s %7d\n" "Total" total
  map read <$> getArgs >>= \ case
    [n, bound, a, b] -> brute bound $ take b $ drop a $ enum n
    [n, bound, a]    -> brute bound $ drop a $ enum n
    [n, bound]       -> brute bound $ enum n
    [n] ->
      print $ length $ enum n
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

-- bb3

-- bb4
-- (Terminated,              49_529_149)
-- (NonTerminated GiveUp,       647_565)
-- (NonTerminated StuckLeft, 16_164_579)
-- (NonTerminated RunAway,   17_710_699)
-- (NonTerminated NoPath,     8_616_376)
-- (NonTerminated Loop,      11_754_926)
-- (NonTerminated TooWide,   15_900_802)
-- (Total,                  120_324_096)

-- Skeletons
-- Terminated  46_039_804  (44.0%)
-- GiveUp         613_403  ( 0.6%)
-- StuckLeft   14_430_267  (13.8%)
-- RunAway     16_801_803  (16.1%)
-- Loop        11_365_166  (10.9%)
-- TooWide     15_405_685  (14.7%)
-- Total      104_656_128

-- Examples ---------------------------------------------------------------

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
bb3 = [ (A, O) :-> (B, O, L)
      , (A, I) :-> (C, I, L)
      , (B, O) :-> (C, I, R)
      , (B, I) :-> (H, O, L)
      , (C, O) :-> (A, I, L)
      , (C, I) :-> (C, O, R) ]

-- Score: 3546, index: 113_180_330
bb4 :: Machine
bb4 = [ (A, O) :-> (A, I, L)
      , (A, I) :-> (B, O, L)
      , (B, O) :-> (C, O, R)
      , (B, I) :-> (C, I, R)
      , (C, O) :-> (A, O, R)
      , (C, I) :-> (D, O, R)
      , (D, O) :-> (H, O, L)
      , (D, I) :-> (B, O, R) ]

-- BB4 analysis
-- A: write 1 and step left until you find a 1
--    if left-border write 0, step R -> C
--    else           write 0, step R -> A
-- C: write 0 and step R, 0->A and 1->D

-- Terminates on A I^59
-- Previous rounds I^43, 31, 22, 15
-- Essentially what happens is
-- - You get to state A in the left-most position
--   with n 1s filling up the tape
-- - You clear it writing a 1 every third 0 (cycling through BCD)
-- - if you end (reach the 0 at the right) on
--    B (n = 0 mod 3): Add three 1s on the right
--    C (n = 1 mod 3): Add two 1s on the right
--    D (n = 2 mod 3): Halt
-- - Move all the (div n 3) stray ones to the right and fill with ones

sim_bb4 :: [Int]
sim_bb4 = go 3
  where
    go n
      | mod n 3 == 2 = [n]
      | otherwise    = n : go (n + stray + extra)
      where
        stray = div (n - 1) 3
        extra | mod n 3 == 0 = 3
              | otherwise    = 2

sim_bb5 :: [Maybe Int] -> [Int]
sim_bb5 extras = go 3
  where
    go n
      | Nothing <- extra = [n]
      | Just e  <- extra = n : go (n + stray + e)
      where
        stray = div (n - 1) 4
        extra = extras !! mod n 4

-- -- Score: 16133, index: 167_887_920
-- bb5 :: Machine
-- bb5 = [ (A,O) :-> (B,O,L)
--       , (A,I) :-> (H,O,L)
--       , (B,O) :-> (C,O,L)
--       , (B,I) :-> (C,O,R)
--       , (C,O) :-> (B,I,L)
--       , (C,I) :-> (D,O,R)
--       , (D,O) :-> (B,O,R)
--       , (D,I) :-> (E,I,R)
--       , (E,O) :-> (B,I,R)
--       , (E,I) :-> (A,I,R) ]

-- -- Score: 17523, index: 350_307_653
-- bb5 :: Machine
-- bb5 = [ (A,O) :-> (B,O,L)
--       , (A,I) :-> (H,O,L)
--       , (B,O) :-> (C,O,R)
--       , (B,I) :-> (D,I,L)
--       , (C,O) :-> (D,O,R)
--       , (C,I) :-> (C,I,R)
--       , (D,O) :-> (A,I,L)
--       , (D,I) :-> (E,O,R)
--       , (E,O) :-> (E,I,L)
--       , (E,I) :-> (B,O,L) ]

-- -- Score: 43642, index: 2_101_290_604
-- bb5 :: Machine
-- bb5 = [ (A,O) :-> (B,O,L)
--       , (A,I) :-> (C,O,L)
--       , (B,O) :-> (D,O,R)
--       , (B,I) :-> (A,O,L)
--       , (C,O) :-> (C,O,R)
--       , (C,I) :-> (B,O,R)
--       , (D,O) :-> (E,I,R)
--       , (D,I) :-> (H,O,L)
--       , (E,O) :-> (B,I,L)
--       , (E,I) :-> (E,I,R) ]

-- -- Score: 64265, index: 5_668_169_472
-- bb5 :: Machine
-- bb5 = [ (A,O) :-> (B,O,L)
--       , (A,I) :-> (C,O,R)
--       , (B,O) :-> (A,I,L)
--       , (B,I) :-> (D,O,R)
--       , (C,O) :-> (E,O,R)
--       , (C,I) :-> (A,O,L)
--       , (D,O) :-> (E,O,R)
--       , (D,I) :-> (H,O,L)
--       , (E,O) :-> (B,O,R)
--       , (E,I) :-> (C,I,R) ]

-- Score: 97461, index: 3_826_129_157
bb5 :: Machine
bb5 = [ (A,O) :-> (B,O,L)
      , (A,I) :-> (C,O,R)
      , (B,O) :-> (D,O,L)
      , (B,I) :-> (H,O,L)
      , (C,O) :-> (E,I,L)
      , (C,I) :-> (C,I,R)
      , (D,O) :-> (C,I,L)
      , (D,I) :-> (A,I,L)
      , (E,O) :-> (A,O,R)
      , (E,I) :-> (A,O,L) ]

-- Score: 71076
bb5Andreas :: Machine
bb5Andreas =
  [ (A,O) :-> (B,O,L)
  , (B,O) :-> (C,O,R)
  , (C,O) :-> (D,I,R)
  , (D,O) :-> (E,I,R)
  , (E,O) :-> (E,I,L)
  , (A,I) :-> (D,O,R)
  , (B,I) :-> (E,O,L)
  , (C,I) :-> (C,O,L)
  , (D,I) :-> (H,O,L)
  , (E,I) :-> (A,O,L) ]

example :: Machine
example = [ (A, O) :-> (B, I, R)
          , (A, I) :-> (B, O, R)
          , (B, O) :-> (C, O, R)
          , (B, I) :-> (H, O, R)
          , (C, O) :-> (C, I, L)
          , (C, I) :-> (A, I, R)
          ]


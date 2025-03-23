module Main where

import Control.Arrow (first)
import Control.Applicative
import Control.Monad
import Data.Bits
import Data.List
import Data.Ord
import Data.Maybe
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
import Test.QuickCheck

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

-- Reachability graphs ----------------------------------------------------

type ReachGraph a = Map a (Set a)

addReachEdge :: Ord a => a -> a -> ReachGraph a -> ReachGraph a
addReachEdge x y g = addYs <$> (Map.insertWith (<>) x (Set.singleton y) g)
  where
    ys = Set.insert y $ fromMaybe mempty (Map.lookup y g)
    addYs zs
      | Set.member x zs = ys <> zs
      | Set.member y zs = ys <> zs
      | otherwise       = zs

-- Smarter running --------------------------------------------------------

data Reason = GiveUp | StuckLeft | RunAway | NoPath | Loop | TooWide
  deriving (Eq, Ord, Show)

data LoopAnalysis = LoopAnalysis
  { leftStuck    :: [(State, Symbol)]
  , runners      :: [State]
  }
  deriving Show

loopAnalysis :: Machine -> LoopAnalysis
loopAnalysis m = LoopAnalysis
  { leftStuck = go [ ((s1, i), (s2, o)) | (s1, i) :-> (s2, o, L) <- m, s2 /= H ]
  , runners   = go [ (s, s') | (s, O) :-> (s', _, R) <- m, s' /= H ]
  }
  where
    go :: Eq a => [(a, a)] -> [a]
    go g
      | g == g'   = is
      | otherwise = go g'
      where
        is  = map fst g
        g'  = [ e | e@(_, o) <- g, elem o is ]

unknown :: Int -> Int -> [Machine]
unknown fuel n = [ m | m <- enum n, Left GiveUp <- [runTo fuel m] ]

runUnknown fuel n i = m <$ vrun fuel m
  where
    m : _ = drop i $ unknown fuel n


loopCheck :: LoopAnalysis -> Int -> Config -> Config -> Maybe Reason
loopCheck loop _ _ (s, tape@(Tape _ [] _))
  | elem (s, look tape) (leftStuck loop) = Just StuckLeft
loopCheck loop _ _ (s, Tape _ _ [])
  | elem s (runners loop) = Just RunAway
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

-- Running multiple machines at once --------------------------------------

-- Idea: Enumerate machines as you run them
-- * That way we don't have to enumerate transitions that are never taken! And there are a lot of
--   machines with unused transitions.
-- * You could also set a min value for termination and not generate a halting transition until that
--   many steps!
-- * Memory is a concern!

unvisited :: Int -> Machine -> Set (State, Symbol)
unvisited fuel m = Set.difference allStates visited
  where
    allStates = Set.fromList [ i | i :-> (s, _, _) <- m, s /= H ]
    visited = snd $ runTo' mempty (\ _ (s, tape) -> Set.insert (s, look tape)) fuel m

data Generator g = Generator
  { initG          :: g
  , genTransitions :: g -> Int -> Config -> [((State, Symbol, Dir), g)]
      -- Called when we need a new transition
  }

dumbGenerator :: Int -> Generator ()
dumbGenerator n = Generator () $ \ _ _ _ -> [((s, o, d), ()) | s <- states, o <- [O, I], d <- [L, R]]
  where
    states = take n [A ..] ++ [H]

data GenSt = GenSt
  { oldStates       :: [(State, Int)] -- number of open transitions in each old state
  , newStates       :: [State]
  , openTransitions :: Int
  , rGraph          :: ReachGraph State
  }
  deriving (Show)

-- BB(3)
-- First implementation
--    Terminated     26668  (68.8%)
--    GiveUp          4294  (11.1%)
--    StuckLeft       2176  ( 5.6%)
--    RunAway         1029  ( 2.7%)
--    Loop            4581  (11.8%)
--    Total          38748
-- Halt reachable
--    Terminated     26668  (74.3%)
--    GiveUp          3312  ( 9.2%)
--    StuckLeft       1519  ( 4.2%)
--    RunAway          629  ( 1.8%)
--    Loop            3768  (10.5%)
--    Total          35896
-- Oops (only HOL)
--    Terminated      6667  (41.9%)
--    GiveUp           715  ( 4.5%)
--    StuckLeft       1519  ( 9.6%)
--    RunAway          629  ( 4.0%)
--    Loop            3768  (23.7%)
--    TooWide         2597  (16.3%)
--    Total          15895
-- Lower bound 45
--    Terminated      5141  (35.8%)
--    GiveUp           715  ( 5.0%)
--    StuckLeft       1519  (10.6%)
--    RunAway          629  ( 4.4%)
--    Loop            3768  (26.2%)
--    TooWide         2597  (18.1%)
--    Total          14369
-- Fixed and improved RunAway
--    Terminated      5168  (35.9%)
--    GiveUp           720  ( 5.0%)
--    StuckLeft       1559  (10.8%)
--    RunAway          710  ( 4.9%)
--    Loop            3796  (26.3%)
--    TooWide         2454  (17.0%)
--    Total          14407

smartGenerator :: Int -> Int -> Generator GenSt
smartGenerator n lo = Generator{..}
  where
    initG = GenSt{..}
      where oldStates       = [(A, 2)]
            newStates       = take (n - 1) [B ..] ++ [H]  -- Halt as the last resort
            openTransitions = 2
            rGraph          = mempty
    genTransitions g@GenSt{..} n (s, look -> i) = do
      let new = take 1 newStates
          states | openTransitions > 1 = new ++ map fst oldStates
                 | otherwise           = new
      s' <- states
      let oldStates' = map dec oldStates
            where dec (s', n) | s == s' = (s', n - 1)
                  dec e                 = e
          (old', new', open')
            | [s'] == new = ((s', 2) : oldStates', drop 1 newStates, openTransitions + 1)
            | otherwise   = (          oldStates',        newStates, openTransitions - 1)
          rg' = addReachEdge s s' rGraph
          exitStates = Set.fromList [ s | (s, n) <- old', n > 0 ]
      -- Don't halt before the lower bound unless we have to
      guard $ or [ n >= lo
                 , s' /= H
                 , openTransitions == 1
                 ]
      -- Make sure every closed state can reach an exit state
      guard $ and [ not $ Set.disjoint rs exitStates
                  | (s, 0) <- old'
                  , let rs = fromMaybe mempty $ Map.lookup s rg'
                  ]
      o <- if s' == H then [O] else [O, I]
      d <- if s' == H then [L] else [L, R]
      pure ((s', o, d), g{ oldStates       = old'
                         , newStates       = new'
                         , openTransitions = open'
                         , rGraph          = rg'
                         })

-- debug = go (initG g)
--   where
--     g = smartGenerator 3
--     step gs (s, i) sod = head [ gs' | (sod', gs') <- genTransitions g gs 0 (s, Tape 0 [] (i : [])), sod' == sod ]
--     go gs [] = gs
--     go gs ((i :-> o) : ts) = go (step gs i o) ts

data LoopDetector l s = LoopDetector
  { emptyL   :: l                -- For an empty machine
  , stepL    :: l -> Rule -> l   -- When adding a new rule
  , initLs   :: s
  , stepLoop :: l -> s -> Int -> Config -> Config -> Either Reason s
  }

noLoopDetector :: LoopDetector () ()
noLoopDetector = LoopDetector () (\ _ _ -> ()) () (\ _ _ _ _ _ -> Right ())

loopDetector :: LoopDetector (Machine, LoopAnalysis) (Set Config)
loopDetector = LoopDetector{..}
  where
    emptyL            = ([], LoopAnalysis mempty mempty)
    stepL (m, _) rule = (rule : m, loopAnalysis (rule : m))
    initLs            = mempty
    stepLoop (_, loop) seen n conf@(_, tape) conf'
      | shouldCache, Set.member conf seen          = Left Loop
      | Just reason <- loopCheck loop n conf conf' = Left reason
      | otherwise                                  = Right seen'
      where
        shouldCache = n < 25 && sz <= 5
        sz = tapeSize tape
        seen' | shouldCache = Set.insert conf seen
              | otherwise   = seen

-- Parameterised over
--  * generator for new transitions
--  * loop detection
-- Problem: can't start in the middle, so not easy to parallelize
runExplore' :: Generator g
            -> LoopDetector l ls
            -> Int
            -> Machine
            -> [(Either Reason Int, Machine)]
runExplore' Generator{..} LoopDetector{..} fuel m =
    go fuel 0 initG initL initLs m initConf
  where
    initL = foldl stepL emptyL m

    go 0 _ _ _ _ m _ = pure (Left GiveUp, reverse m)
    go _ n _ _ _ m (H, _) = pure (Right n, reverse m)
    go fuel !n g l ls m conf@(s, tape) = do
      let step = case [ sod | si :-> sod <- m, si == (s, i) ] of
            []  -> do
              -- Add new transition
              (sod, g') <- genTransitions g n conf
              let rule = (s, i) :-> sod
              pure (rule : m, g', stepL l rule, sod)
            sod : _ -> pure (m, g, l, sod)
      (m', g', l', (s', o, d)) <- step
      let conf' = (s', move d $ write o tape)
      case stepLoop l' ls n conf conf' of
        Left r    -> pure (Left r, reverse m')
        Right ls' -> go (fuel - 1) (n + 1) g' l' ls' m' conf'
      where
        i = look tape

naiveExplore :: Int -> Int -> [(Either Reason Int, Machine)]
naiveExplore n fuel = runExplore' (dumbGenerator n) noLoopDetector fuel []

explore :: Int -> Int -> Int -> [(Either Reason Int, Machine)]
explore n lo fuel = runExplore' (smartGenerator n lo) loopDetector fuel []

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

    go' i best tms stats
      | mod i 1000000 == 0 = trace (show i) $ go i best tms stats
      | otherwise          = go i best tms stats

bruteExplore :: [(Either Reason Int, Machine)] -> ([(Int, Int, Machine)], Stats)
bruteExplore xs = go 0 (zip [1..] xs) mempty
  where
    addStat k = Map.insertWith (+) k 1
    go best [] stats = ([], stats)
    go best ((i, (Left r, _)) : ms) !stats = go' best ms (addStat (NonTerminated r) stats)
    go best ((i, (Right n, m)) : ms) !stats
      | n > best = first ((n, i, m):) $ go' n ms stats'
      | otherwise = go' best ms stats'
      where
        stats' = addStat Terminated stats

    go' best ms@((i, _) : _) stats
      | mod i 1000000 == 0 = trace (show i) $ go best ms stats
    go' best ms stats = go best ms stats

bruteIO :: ([(Int, Int, Machine)], Stats) -> IO (Int, Int, Machine)
bruteIO (ms, stats) = do
  mapM_ print ms
  let why Terminated = "Terminated"
      why (NonTerminated r) = show r
      total = sum stats
  sequence_ [ printf "%-10s %9d  (%4.1f%%)\n" (why r) n (100 * fromIntegral @_ @Double n / fromIntegral total)
            | (r, n) <- Map.toList stats ]
  printf "%-10s %9d\n" "Total" total
  pure (last ms)

main :: IO ()
main = do
  let brute bound ms0 = () <$ bruteIO (bruteForce bound ms0)
  map read <$> getArgs >>= \ case
    [n, bound, a, b] -> brute bound $ take b $ drop a $ enum n
    -- [n, bound, a]    -> brute bound $ drop a $ enum n
    [n, lo, bound]    ->
      () <$ bruteIO (bruteExplore $ explore n lo bound)
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
-- Terminated    123,609  (47.0%)
-- GiveUp            784  ( 0.3%)
-- StuckLeft      37,423  (14.2%)
-- RunAway        46,555  (17.7%)
-- Loop           22,124  ( 8.4%)
-- TooWide        32,385  (12.3%)
-- Total         262,880

-- BB(4) (fuel: 10,000)
-- (Terminated,              49,529,149)
-- (NonTerminated GiveUp,       647,565)
-- (NonTerminated StuckLeft, 16,164,579)
-- (NonTerminated RunAway,   17,710,699)
-- (NonTerminated NoPath,     8,616,376)
-- (NonTerminated Loop,      11,754,926)
-- (NonTerminated TooWide,   15,900,802)
-- (Total,                  120,324,096)

-- Skeletons (13m30s)
--    Terminated  46,039,804  (44.0%)
--    GiveUp         613,403  ( 0.6%)
--    StuckLeft   14,430,267  (13.8%)
--    RunAway     16,801,803  (16.1%)
--    Loop        11,365,166  (10.9%)
--    TooWide     15,405,685  (14.7%)
--    Total      104,656,128

-- Explore (2m41s)
--    Terminated    932,925  (37.6%)
--    GiveUp        237,981  ( 9.6%)
--    StuckLeft     166,432  ( 6.7%)
--    RunAway        73,188  ( 2.9%)
--    Loop          675,060  (27.2%)
--    TooWide       395,934  (16.0%)
--    Total       2,481,520

-- Lower bound 3500 (2m40s)
--    Terminated    756,284  (32.8%)
--    GiveUp        237,981  (10.3%)
--    StuckLeft     166,432  ( 7.2%)
--    RunAway        73,188  ( 3.2%)
--    Loop          675,060  (29.3%)
--    TooWide       395,934  (17.2%)
--    Total       2,304,879

-- Fixed RunAway (2m38s)
--    Terminated    761,834  (32.9%)
--    GiveUp        239,243  (10.3%)
--    StuckLeft     173,502  ( 7.5%)
--    RunAway        80,837  ( 3.5%)
--    Loop          682,361  (29.4%)
--    TooWide       380,319  (16.4%)
--    Total       2,318,096

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

-- -- Score: 97461, index: 3_826_129_157
-- bb5 :: Machine
-- bb5 = [ (A,O) :-> (B,O,L)
--       , (A,I) :-> (C,O,R)
--       , (B,O) :-> (D,O,L)
--       , (B,I) :-> (H,O,L)
--       , (C,O) :-> (E,I,L)
--       , (C,I) :-> (C,I,R)
--       , (D,O) :-> (C,I,L)
--       , (D,I) :-> (A,I,L)
--       , (E,O) :-> (A,O,R)
--       , (E,I) :-> (A,O,L) ]

-- -- Score: 115854, index: 4_082_614_040
bb5 :: Machine
bb5 = [ (A,O) :-> (B,O,L)
      , (A,I) :-> (C,O,R)
      , (B,O) :-> (D,O,L)
      , (B,I) :-> (A,I,L)
      , (C,O) :-> (A,I,R)
      , (C,I) :-> (E,O,R)
      , (D,O) :-> (E,I,R)
      , (D,I) :-> (H,O,L)
      , (E,O) :-> (C,O,R)
      , (E,I) :-> (A,I,R) ]

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

-- QuickCheck tests -------------------------------------------------------

instance Arbitrary State where
  arbitrary = elements [A .. F]

genGraph :: Gen (ReachGraph State)
genGraph = foldr (uncurry addReachEdge) mempty <$> (listOf ((,) <$> elements [A .. F] <*> elements [A .. F]))

prop_reach_idem :: [(State, State)] -> State -> State -> Property
prop_reach_idem es s1 s2 = add g === add (add g)
  where
    g = foldr (uncurry addReachEdge) mempty es
    add = addReachEdge s1 s2

prop_reach :: [(State, State)] -> Property
prop_reach es = whenFail (print g) $ bad === []
  where
    g = foldr (uncurry addReachEdge) mempty es
    bad = [ (s, s')
          | (s, ss) <- Map.toList g
          , s' <- Set.toList ss
          , let ss' = fromMaybe mempty $ Map.lookup s' g
          , not $ Set.isSubsetOf ss' ss
          ]

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

data RLE a = RLE a {-# UNPACK #-} !Int
  deriving (Eq, Ord, Show, Functor)

newtype RList a = RList [RLE a]
  deriving (Eq, Ord, Show, Functor)

instance Eq a => Semigroup (RList a) where
  RList [] <> ys = ys
  RList [RLE x n] <> RList (RLE y m : ys)
    | x == y = RList (RLE y (n + m) : ys)
  RList (x : xs) <> RList ys = RList (x : zs)
    where
      RList zs = RList xs <> RList ys

instance Eq a => Monoid (RList a) where
  mempty = RList []

expand :: RList a -> [a]
expand (RList xs) = concat [ replicate n x | RLE x n <- xs ]

lengthR :: RList a -> Int
lengthR (RList xs) = sum [ n | RLE _ n <- xs ]

consR :: Eq a => a -> RList a -> RList a
consR x (RList []) = RList [RLE x 1]
consR x (RList xs@(RLE y n : ys))
  | x == y    = RList (RLE y (n + 1) : ys)
  | otherwise = RList (RLE x 1 : xs)

headR :: RList a -> Maybe a
headR (RList []) = Nothing
headR (RList (RLE x _ : _)) = Just x

dropR :: Int -> RList a -> RList a
dropR 0 xs = xs
dropR n (RList (RLE x m : xs))
  | n < m     = RList (RLE x (m - n) : xs)
  | otherwise = dropR (n - m) (RList xs)

unconsR :: RList a -> Maybe (a, RList a)
unconsR (RList []) = Nothing
unconsR (RList (RLE x n : xs))
  | n > 1     = Just (x, RList (RLE x (n - 1) : xs))
  | otherwise = Just (x, RList xs)

pattern (:@) :: Eq a => a -> RList a -> RList a
pattern x :@ xs <- (unconsR -> Just (x, xs))
  where
    x :@ xs = consR x xs

pattern NilR = RList []

{-# COMPLETE NilR, (:@) #-}

type Tape = Tape' Symbol
data Tape' a = Tape {-# UNPACK #-} !Int (RList a) (RList a)
  deriving (Eq, Ord, Show)

tape0 :: (Eq a, Enum a) => Tape' a
tape0 = Tape 0 mempty mempty

look :: Tape -> Symbol
look (Tape _ _ NilR)    = O
look (Tape _ _ (x :@ _)) = x

write :: Symbol -> Tape -> Tape
write O (Tape n ls    NilR)     = Tape n ls       NilR
write I (Tape n ls    NilR)     = Tape n ls (I :@ NilR)
write O (Tape n ls (_ :@ NilR)) = Tape n ls       NilR
write x (Tape n ls (_ :@ rs))   = Tape n ls (x :@   rs)

-- we can move (L)eft or (R)ight on a Tape

data Dir = L | R
  deriving ( Eq, Ord, Show, Enum )

move :: Dir -> Tape -> Tape
move L (Tape n  NilR          rs)  = Tape 0           NilR           rs -- bouncing
move L (Tape n (O :@ ls)    NilR)  = Tape (n - 1)       ls         NilR
move L (Tape n (x :@ ls)      rs)  = Tape (n - 1)       ls     (x :@ rs)
move R (Tape n  ls      (x :@ rs)) = Tape (n + 1) (x :@ ls)    rs
move R (Tape n  ls          NilR)  = Tape (n + 1) (O :@ ls)  NilR

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
vizrun w fuel rls !n conf@(s, Tape ln (expand -> ls) rrs) = do
  putStrLn
    $ printf "%4d " ln
   ++ concat [ " " ++ show x ++ " " | x <- take (div (w - 5) 3) $ reverse ls ]
   ++ "\ESC[31m" ++ show s ++ "\ESC[0m"
   ++ concat [ show x ++ "  " | x <- take (max 0 $ div (w - 5) 3 - ln) rs ]
  case rules rls conf of
    Nothing    -> return (n, conf)
    Just conf' -> vizrun w (fuel - 1) rls (n + 1) conf'
  where
    rs = pad $ expand rrs
    pad [] = [O]
    pad rs = rs

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
loopCheck loop _ _ (s, tape@(Tape _ NilR _))
  | elem (s, look tape) (leftStuck loop) = Just StuckLeft
loopCheck loop _ _ (s, Tape _ _ NilR)
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
tapeSize (Tape n ls rs) = n + lengthR rs

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

traceRun :: Machine -> [Config]
traceRun m = traceRun' m (A, tape0)

traceRun' :: Machine -> Config -> [Config]
traceRun' m = go
  where
    go conf =
      case rules m conf of
        Nothing    -> [conf]
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
  , curRules        :: Machine
  }
  deriving (Show)

smartGenerator :: Int -> Int -> Generator GenSt
smartGenerator n lo = Generator{..}
  where
    initG = GenSt{..}
      where oldStates       = [(A, 2)]
            newStates       = take (n - 1) [B ..] ++ [H]  -- Halt as the last resort
            openTransitions = 2
            rGraph          = mempty
            curRules        = []
    genTransitions g@GenSt{..} n (s, look -> i) = do
      let new = take 1 newStates
          states | openTransitions > 1 = new ++ map fst oldStates
                 | otherwise           = new
      s' <- states
      let oldStates' = map dec oldStates
            where dec (s', n) | s == s' = (s', n - 1)
                  dec e                 = e
          isNew = [s'] == new
          (old', new', open')
            | isNew     = ((s', 2) : oldStates', drop 1 newStates, openTransitions + 1)
            | otherwise = (          oldStates',        newStates, openTransitions - 1)
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

      -- (A, O) :-> (s, O, L) is never good, just make s the starting state!
      -- Not technically true, if you have a (s, O) :-> (A, O, L) transition you can
      -- buy an extra step by making s the starting state.
      guard $ (s, i, o, d) /= (A, O, O, L)

      let rules' = (s, i) :-> (s', o, d) : curRules

      -- Don't create equivalent states
      guard $ not $ hasEquivalentState s' rules'

      pure ((s', o, d), g{ oldStates       = old'
                         , newStates       = new'
                         , openTransitions = open'
                         , rGraph          = rg'
                         , curRules        = rules'
                         })

hasEquivalentState :: State -> Machine -> Bool
hasEquivalentState s m =
  case rep s of
    Just r | not $ null equiv -> True
      where
        equiv = [ s' | s' <- states, s' /= s
                     , Just r' <- [rep s']
                     , r =~ r' ]
    _ -> False
  where
    states = nub [ s | (s, _) :-> _ <- m ]
    rep s = case sort [ (i, o) | (s', i) :-> o <- m,  s == s' ] of
              [(O, o1), (I, o2)] -> Just (s, o1, o2)
              _                  -> Nothing
    (s, o1, o2) =~ (s', o1', o2') = eq o1 o1' && eq o2 o2'
      where
        eq o o' = r o == r o'
        r (s0, o, d)
          | s0 == s || s0 == s' = (Nothing, o, d) -- self transition
          | otherwise           = (Just s0, o, d)

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
      (m', g', l', sod@(s', _, _)) <- step
      let (tape', m) = applyRule s sod tape
          conf' = (s', tape')
      case stepLoop l' ls n conf conf' of
        Left r    -> pure (Left r, reverse m')
        Right ls' -> go (fuel - m) (n + m) g' l' ls' m' conf'
      where
        i = look tape

{-# INLINE applyRule #-}
applyRule :: State -> (State, Symbol, Dir) -> Tape -> (Tape, Int)
applyRule s (s', o, R) tape@(Tape w ls rs) =
  case rs of
    RList []              -> (Tape (w + 1) (o :@ ls) rs, 1)
    RList (RLE i n : rs)
      | s == s'   -> (Tape (w + n) (RList [RLE o n] <> ls) (RList rs), n)
      | otherwise -> (move R $ write o tape, 1)
-- applyRule _ (_, o, R) tape = (move R $ write o tape, 1)
applyRule s (s', o, L) tape@(Tape w (RList (RLE i n : ls)) (j :@ rs))
  | s == s', i == j = (tape', n)
  where tape' = Tape (w - n) (RList ls) $ i :@ add o rs
        add O NilR = NilR
        add o rs   = RList [RLE o n] <> rs
applyRule _ (_, o, L) tape = (move L $ write o tape, 1)
-- applyRule _ (_, o, d) tape = (move d $ write o tape, 1)

runSteps :: Int -> Machine -> (Either Reason Int, Int)
runSteps fuel m = go fuel 0 0 (A, tape0)
  where
    go 0 _ steps _ = (Left GiveUp, steps)
    go fuel n steps (H, _) = (Right n, steps)
    go fuel !n !steps (s, tape) = go (fuel - n') (n + n') (steps + 1) (s', tape')
      where
        i = look tape
        sod@(s', _, _) : _ = [o | si :-> o <- m, si == (s, i)]
        (tape', n') = applyRule s sod tape

-- Plan:
--  * Make exploration state explicit, to enable resuming from a given state
--  * Add parallelize
--  * Terminal gui with live updated stats, and ability to stop and write state to disk

naiveExplore :: Int -> Int -> [(Either Reason Int, Machine)]
naiveExplore n fuel = runExplore' (dumbGenerator n) noLoopDetector fuel []

explore :: Int -> Int -> Int -> [(Either Reason Int, Machine)]
explore n lo fuel = runExplore' (smartGenerator n lo) loopDetector fuel []

-- Macro machines ---------------------------------------------------------

-- The Dir is which direction we're moving (i.e. if dir is L we are looking at the right end of the
-- macro symbol). We also need to know if we're at the left end of the tape!
type MacroSymbol = [Symbol]
data Wall = LeftWall | NoWall
  deriving (Eq, Ord, Show)
type MacroMachine = Map (State, MacroSymbol, Dir, Wall) (State, MacroSymbol, Dir, Int)

compileMacroStep :: Machine -> (State, MacroSymbol, Dir, Wall) -> Either Reason (State, MacroSymbol, Dir, Int)
compileMacroStep m (s, is, d, w) = go fuel 0 (s, tape)
  where
    tape | d == R    = ([], is)
         | otherwise = (ls, [r])
      where r : ls = reverse is
    n = length $ nub [ s | (s, _) :-> _ <- m ]
    fuel = n * (2 ^ length is)

    move L ([], rs)     = ([], rs)
    move L (l : ls, rs) = (ls, l : rs)
    move R (ls, r : rs) = (r : ls, rs)

    go 0 n (s, tape) = Left GiveUp
    go fuel n (H, _) = Right (H, [], R, n)
    go fuel !n (s, (ls, i : rs))
      | d == L, null ls, w == NoWall = Right (s', o : rs, L, n + 1)
      | d == R, null rs              = Right (s', reverse (o : ls), R, n + 1)
      | otherwise                    = go (fuel - 1) (n + 1) (s', move d (ls, o : rs))
      where
        (s', o, d) : _ = [o | si :-> o <- m, si == (s, i)]

runMacro :: Int -> Int -> Machine -> (Either Reason Int, Int, MacroMachine)
runMacro k fuel m = go mempty fuel 0 0 (A, R, ([], []))
  where
    look (_, i : _) = i
    look (_, [])    = replicate k O

    wall ([], _) = LeftWall
    wall _       = NoWall

    write x (ls, _ : rs) = (ls, x : rs)
    write x (ls, [])     = (ls, [x])

    move L ([], rs)     = ([], rs)
    move L (l : ls, rs) = (ls, l : rs)
    move R (ls, r : rs) = (r : ls, rs)

    go mm 0 _ steps _ = (Left GiveUp, steps, mm)
    go mm fuel n steps (H, _, _) = (Right n, steps, mm)
    go mm fuel !n !steps conf@(s, d, tape@(look -> i)) =
        go mm' (fuel - n') (n + n') (steps + 1) (s', d', tape')
      where
        sid = (s, i, d, wall tape)
        ((s', o, d', n'), mm') =
          case Map.lookup sid mm of
            Just o  -> (o, mm)
            Nothing -> (o, Map.insert sid o mm)
              where Right o = compileMacroStep m sid
        tape' = move d' $ write o tape

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

-- BB(3)
-- First implementation of smartGenerator
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
-- Don't go (A, O) :-> (_, O, L)
--    Terminated      4471  (37.0%)
--    GiveUp           616  ( 5.1%)
--    StuckLeft       1252  (10.4%)
--    RunAway          634  ( 5.2%)
--    Loop            2934  (24.3%)
--    TooWide         2175  (18.0%)
--    Total          12082
-- No equivalent states
--    Terminated      4471  (37.0%)
--    GiveUp           616  ( 5.1%)
--    StuckLeft       1250  (10.4%)
--    RunAway          634  ( 5.3%)
--    Loop            2932  (24.3%)
--    TooWide         2173  (18.0%)
--    Total          12076

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

-- Fixed RunAway
--  2m38s
--    Terminated    761,834  (32.9%)
--    GiveUp        239,243  (10.3%)
--    StuckLeft     173,502  ( 7.5%)
--    RunAway        80,837  ( 3.5%)
--    Loop          682,361  (29.4%)
--    TooWide       380,319  (16.4%)
--    Total       2,318,096

-- Don't go (A, O) :-> (_, O, L)
--  2m12s
--    Terminated    641,264  (33.3%)
--    GiveUp        199,594  (10.4%)
--    StuckLeft     143,237  ( 7.4%)
--    RunAway        71,888  ( 3.7%)
--    Loop          538,475  (27.9%)
--    TooWide       333,648  (17.3%)
--    Total       1,928,106

-- No equivalent states
--  2m12s
--    Terminated    640,502  (33.3%)
--    GiveUp        198,448  (10.3%)
--    StuckLeft     142,953  ( 7.4%)
--    RunAway        71,864  ( 3.7%)
--    Loop          537,139  (27.9%)
--    TooWide       332,776  (17.3%)
--    Total       1,923,682

-- RLE
--  2m12s       normal list implementation
--  2m47s       bulk nothing
--  3m22s       bulk R    why is this so much slower?! the matching!
--  3m25s       also bulk L

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
-- bb5 :: Machine
-- bb5 = [ (A,O) :-> (B,O,L)
--       , (A,I) :-> (C,O,R)
--       , (B,O) :-> (D,O,L)
--       , (B,I) :-> (A,I,L)
--       , (C,O) :-> (A,I,R)
--       , (C,I) :-> (E,O,R)
--       , (D,O) :-> (E,I,R)
--       , (D,I) :-> (H,O,L)
--       , (E,O) :-> (C,O,R)
--       , (E,I) :-> (A,I,R) ]

-- -- Score: 161,279, index: 10,125,304 (explore)
-- bb5 :: Machine
-- bb5 = [ (A,O) :-> (B,O,L)
--       , (B,O) :-> (C,O,L)
--       , (C,O) :-> (A,I,L)
--       , (A,I) :-> (D,O,L)
--       , (D,O) :-> (B,I,L)
--       , (B,I) :-> (E,I,L)
--       , (E,I) :-> (C,O,R)
--       , (C,I) :-> (E,O,R)
--       , (E,O) :-> (C,I,R)
--       , (D,I) :-> (H,O,L) ]

-- -- Score: 161,537, index: 12,983,337 (explore)
-- bb5 :: Machine
-- bb5 = [ (A,O) :-> (B,O,L)
--       , (B,O) :-> (C,O,R)
--       , (C,O) :-> (D,O,L)
--       , (D,O) :-> (C,I,L)
--       , (C,I) :-> (E,O,R)
--       , (E,O) :-> (B,I,R)
--       , (E,I) :-> (D,O,R)
--       , (B,I) :-> (C,O,L)
--       , (D,I) :-> (A,I,R)
--       , (A,I) :-> (H,O,L) ]

-- -- Score: 187,801, index: 82,851,639
-- bb5 :: Machine
-- bb5 = [ (A,O) :-> (B,O,R)
--       , (B,O) :-> (C,I,R)
--       , (C,O) :-> (A,I,L)
--       , (A,I) :-> (D,O,L)
--       , (D,O) :-> (B,O,L)
--       , (C,I) :-> (D,O,R)
--       , (D,I) :-> (E,O,R)
--       , (E,O) :-> (A,I,R)
--       , (B,I) :-> (C,O,L)
--       , (E,I) :-> (H,O,L) ]

-- Score: 449,336, index: 7,740,790
bb5 :: Machine
bb5 = [ (A,O) :-> (B,O,R)
      , (B,O) :-> (C,O,L)
      , (C,O) :-> (D,I,R)
      , (D,O) :-> (B,I,L)
      , (B,I) :-> (A,I,R)
      , (A,I) :-> (B,I,R)
      , (C,I) :-> (D,O,R)
      , (D,I) :-> (E,I,R)
      , (E,I) :-> (C,O,R)
      , (E,O) :-> (H,O,L) ]

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

-- The traditional (infinite both ways) bb5
-- Terminates in 14 steps on our tapes
bb5vanilla :: Machine
bb5vanilla =
  [ (A,O) :-> (B,I,R)
  , (A,I) :-> (C,I,L)
  , (B,O) :-> (C,I,R)
  , (B,I) :-> (B,I,R)
  , (C,O) :-> (D,I,R)
  , (C,I) :-> (E,O,L)
  , (D,O) :-> (A,I,L)
  , (D,I) :-> (D,I,L)
  , (E,O) :-> (H,I,R)
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
  arbitrary = elements [A .. H]

instance Arbitrary Symbol where
  arbitrary = elements [O, I]
  shrink O = []
  shrink I = [O]

instance Arbitrary Dir where
  arbitrary = elements [L, R]
  shrink L = []
  shrink R = [L]

instance Arbitrary a => Arbitrary (RLE a) where
  arbitrary = RLE <$> arbitrary <*> choose (1, 10)
  shrink (RLE x n) = [ RLE x n | x <- shrink x ] ++
                     [ RLE x n | n <- shrink n, n > 0 ]

instance (Eq a, Arbitrary a) => Arbitrary (RList a) where
  arbitrary = mconcat . map (RList . (:[])) <$> arbitrary
  shrink (RList rs) = mconcat . map (RList . (:[])) <$> shrink rs

instance Arbitrary Tape where
  arbitrary = do
    ls <- arbitrary
    rs <- arbitrary
    pure $ Tape (lengthR ls) ls rs
  shrink (Tape _ ls rs) =
    [ Tape (lengthR ls) ls rs | ls <- shrink ls ] ++
    [ Tape (lengthR ls) ls rs | rs <- shrink rs ]

instance Arbitrary Rule where
  arbitrary = (:->) <$> arbitrary <*> arbitrary
  shrink (i :-> o) = [ i :-> o | o <- shrink o ]

genGraph :: Gen (ReachGraph State)
genGraph = foldr (uncurry addReachEdge) mempty <$> (listOf ((,) <$> elements [A .. F] <*> elements [A .. F]))

genMachine :: Int -> Gen Machine
genMachine n = go [ (s, i) | s <- states, i <- [O, I] ]
  where
    states = take n [A ..]
    go [] = pure []
    go (i : is) = do
      sod <- arbitrary
      rs  <- go is
      pure (i :-> sod : rs)

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

prop_bulk :: Int -> Config -> Property
prop_bulk n conf@(s, tape@(look -> i)) =
  forAllShrink (genMachine n) shrink $ \ m ->
  case [ (s', o, d) | i0 :-> (s', o, d) <- m, i0 == (s, i) ] of
    [] -> False ==> True
    (s', o, d) : _ ->
      collect (min steps 2) $
      whenFail (printf "steps=%d\n" steps) $
        (s', tape') === traceRun' m conf !! steps
      where
        (tape', steps) = applyRule s (s', o, d) tape


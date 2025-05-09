
module Turing.Machine.Macro where

import Control.Applicative
import Control.Monad
import Data.List (nub, sort)
import Data.List.Compressed qualified as CList
import Data.List.Compressed (CList, pattern NilC, pattern (:@))
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Maybe
import Data.ReachGraph
import Text.Pretty
import Text.Printf
import Test.QuickCheck.Extra
import Debug.Trace

import Turing.Types
import Turing.Tape
import Turing.Machine


------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

type LHS = Tape
type RHS = Tape
data MacroClause = LHS :=> (RHS, Dir)
                 | BatchL (CList Symbol) LHS RHS (CList Symbol)
                 | BatchR LHS (CList Symbol) (CList Symbol) RHS
  deriving (Eq, Ord, Show)
data MacroRule = Rule MacroClause State Int
  deriving (Eq, Ord, Show)
newtype MacroMachine = MacroMachine (Map State [MacroRule])
  deriving Show

rules :: MacroMachine -> State -> [MacroRule]
rules (MacroMachine m) s = fromMaybe [] $ Map.lookup s m

addRule :: State -> MacroRule -> MacroMachine -> MacroMachine
addRule s r (MacroMachine m) = MacroMachine $ Map.insertWith ins s [r] m
  where
    ins rs1 rs2 = rs1 ++ filter (not . subsumed) rs2
      where subsumed r = any (`subsumes` r) rs1
    subsumes (Rule (lhs :=> _) _ _) (Rule (lhs' :=> _) _ _) = lhs == lhs'
    subsumes _ _ = False

ruleCost :: MacroRule -> Int
ruleCost (Rule _ _ w) = w

instance Semigroup MacroMachine where
  MacroMachine m <> MacroMachine m' = MacroMachine $ Map.unionWith (++) m m'

instance Monoid MacroMachine where
  mempty = MacroMachine mempty

------------------------------------------------------------------------
-- Building macro rules
------------------------------------------------------------------------

basicRule :: Rule -> MacroRule
basicRule ((_, i) :-> (s', o, d)) =
  Rule (Tape mempty i mempty :=> (Tape mempty o mempty, d)) s' 1

fromPrimRule :: Rule -> MacroMachine
fromPrimRule r@((s, _) :-> (s', o, d)) =
  MacroMachine $ Map.singleton s [basicRule r]

fromPrim :: Machine -> MacroMachine
fromPrim = foldMap fromPrimRule

toPrim :: MacroMachine -> Machine
toPrim (MacroMachine m) = [ (s, i) :-> (s', o, d) | (s, rs) <- Map.toList m, Rule (Tape NilC i NilC :=> (Tape NilC o NilC, d)) s' 1 <- rs ]

-- Combining rules --------------------------------------------------------

plugLHS :: CList Symbol -> LHS -> CList Symbol -> LHS
plugLHS = plugRHS

plugRHS :: CList Symbol -> RHS -> CList Symbol -> Tape
plugRHS ls0 (Tape ls x rs) rs0 = Tape (ls <> ls0) x (rs <> rs0)

-- Rule combination
--  lhs₁ => rhs₁ d₁
--  lhs₂ => rhs₂ d₂
--  (ls₂, rs₂) <- match lhs₂ (move d₁ lp₁[rhs₁]rp₁)
--  ---------------
--  lp₁[lhs₁]rp₁ => ls₂[rhs₂]rs₂ d₂

-- Find lp and rp such that matchLHS lhs (move d lp[rhs]rp) == Just (ls, rs)
chainMatch :: LHS -> RHS -> Dir -> Maybe ((CList Symbol, CList Symbol), (CList Symbol, CList Symbol))

chainMatch (Tape lp x rp) (Tape ls y rs) L = do
  ((rp₁, lp₁), (rs₁, ls₁)) <- chainMatch (Tape rp x lp) (Tape rs y ls) R
  pure ((lp₁, rp₁), (ls₁, rs₁))

chainMatch (Tape lp x rp) (Tape ls y NilC) R
  | Just (lp₁, ls₁) <- CList.dropEitherPrefix lp (y :@ ls) = Just ((lp₁, rp₁), (ls₁, rs₁))
  where
    rp₁ = x :@ rp
    rs₁ = NilC

chainMatch (Tape lp x rp) (Tape ls y (r :@ rs)) R
  | x == r
  , Just (lp₁, ls₁) <- CList.dropEitherPrefix lp (y :@ ls)
  , Just (rp₁, rs₁) <- CList.dropEitherPrefix rp rs = Just ((lp₁, rp₁), (ls₁, rs₁))
chainMatch _ _ _ = Nothing

combineRules :: MacroRule -> MacroRule -> Maybe MacroRule
combineRules (Rule c₁ _ w₁) (Rule c₂ s₂ w₂) = do
  c <- combineClauses c₁ c₂
  pure $ Rule c s₂ (w₁ + w₂)

combineClauses :: MacroClause -> MacroClause -> Maybe MacroClause
combineClauses (lhs₁ :=> (rhs₁, d₁))
               (lhs₂ :=> (rhs₂, d₂))
  | Just ((lp₁, rp₁), (ls₂, rs₂)) <- chainMatch lhs₂ rhs₁ d₁ = do
    let lhs@(Tape lp _ rp) = plugLHS lp₁ lhs₁ rp₁
        rhs = plugRHS ls₂ rhs₂ rs₂
    guard $ CList.length lp + CList.length rp < 10
    pure $ lhs :=> (rhs, d₂)
combineClauses _ _ = Nothing

-- Batching ---------------------------------------------------------------

batchRight :: LHS -> RHS -> Maybe (CList Symbol, CList Symbol)
batchRight (Tape lp x rp) (Tape ls y rs)
  | Just rp₂ <- CList.dropPrefix rs (x :@ rp)
  , Just ls₂ <- CList.dropPrefix lp (y :@ ls) = Just (ls₂, rp₂)
batchRight _ _ = Nothing

batchLeft :: LHS -> RHS -> Maybe (CList Symbol, CList Symbol)
batchLeft (Tape lp x rp) (Tape ls y rs) = do
  (rs₂, lp₂) <- batchRight (Tape rp x lp) (Tape rs y ls)
  pure (lp₂, rs₂)

batchRule :: State -> MacroRule -> [MacroRule]
batchRule s rule@(Rule (lhs :=> (rhs, R)) s' w)
  | s == s'
  , Just (ls, rp) <- batchRight lhs rhs
  , not $ null rp = [Rule (BatchR lhs rp ls rhs) s w, rule]
batchRule s rule@(Rule (lhs :=> (rhs, L)) s' w)
  | s == s'
  , Just (lp, rs) <- batchLeft lhs rhs
  , not $ null lp = [Rule (BatchL lp lhs rhs rs) s w, rule]
batchRule _ rule = [rule]

------------------------------------------------------------------------
-- Running
------------------------------------------------------------------------

matchLHS :: LHS -> Tape -> Maybe (CList Symbol, CList Symbol)
matchLHS (Tape lp x rp) (Tape ls y rs)
  | x == y
  , Just ls' <- CList.dropPrefix lp ls
  , Just rs' <- CList.dropPrefix rp rs = pure (ls', rs')
matchLHS _ _ = Nothing

macroRule :: MacroRule -> Config -> Maybe (Int, MacroRule, Config)
macroRule r (_, tape) = do
  (n, conf) <- match r tape
  pure (n, r, conf)
  where
    match (Rule (lhs :=> (rhs, d)) s1 w) tape = do
      (ls, rs) <- matchLHS lhs tape
      pure (w, (s1, move d $ plugRHS ls rhs rs))
    match rule@(Rule (BatchR (Tape lp x rp) rp₂ ls₂ (Tape ls y rs)) s1 w) tape@(Tape l z r) = do
      guard $ x == z
      l₁ <- CList.dropPrefix lp l
      r₁ <- CList.dropPrefix rp r
      let (r₂, n) = CList.dropRepeatedPrefix rp₂ r₁
      guard $ n > 3
      let result = move R $ Tape (ls <> CList.concatReplicate n ls₂ <> l₁) y (rs <> r₂)
      pure ((n + 1) * w, (s1, result))
    match rule@(Rule (BatchL lp₂ (Tape lp x rp) (Tape ls y rs) rs₂) s1 w) tape@(Tape l z r) = do
      guard $ x == z
      l₁ <- CList.dropPrefix lp l
      r₁ <- CList.dropPrefix rp r
      let (l₂, n) = CList.dropRepeatedPrefix lp₂ l₁
      guard $ n > 3
      let result = move L $ Tape (ls <> l₂) y (rs <> CList.concatReplicate n rs₂ <> r₁)
      pure ((n + 1) * w, (s1, result))

macroStep :: MacroMachine -> Config -> Maybe (Int, MacroRule, Config)
macroStep m conf@(s, _) = foldr (<|>) Nothing [ macroRule r conf | r <- rules m s ]

macroRun :: Int -> MacroMachine -> (Result, MacroMachine)
macroRun = macroRun' False

verboseRun :: Int -> MacroMachine -> (Result, MacroMachine)
verboseRun = macroRun' True

data Reason = OutOfFuel
            | StuckLeft
            | Loop
  deriving (Eq, Ord, Show)

data Result = Terminated Int Int
            | NoTermination Reason Int
  deriving (Eq, Ord, Show)
  deriving Pretty via (ViaShow Result)

resultSteps :: Result -> Int
resultSteps (Terminated _ k) = k
resultSteps (NoTermination _ k) = k

type LastRules = [(State, MacroRule)]

combineStep :: LastRules
            -> MacroMachine
            -> Config
            -> Maybe (Int, LastRules, MacroMachine, Config)
combineStep lastRules m conf@(s, _) =
  case macroStep m conf of
    Nothing           -> Nothing
    Just (w, r, conf) -> Just (w, lastRules', m', conf)
      where
        newRules = do
          (s0, r0) <- lastRules
          Just r'  <- pure $ combineRules r0 r
          pure (s0, r')
        m' = foldr addNew m newRules
        lastRules' = (s, r) : newRules
        addNew (s0, r') m = foldr (addRule s0) m (batchRule s0 r')

macroRun' :: Bool -> Int -> MacroMachine -> (Result, MacroMachine)
macroRun' verbose fuel m0 = goV m0 [] fuel 0 0 initialConfig
  where
    goV m lastRule fuel n k conf@(s, tape) = dbg $ go m lastRule fuel n k conf
      where
        dbg | verbose   = trace $ printf "%7d %3d | %s: %s" n k (show s) (show $ pPrint tape)
            | otherwise = id

    go m _ fuel _ k _ | fuel <= 0 = (NoTermination OutOfFuel k, m)
    go m _ _ n k (H, _) = (Terminated n k, m)
    go m lastRule fuel !n !k conf@(s, _) =
      case combineStep lastRule m conf of
        Nothing                     -> error $ show $ "step failed on" <+> pPrint conf
        Just (w, lastRule, m, conf) -> goV m lastRule (fuel - w) (n + w) (k + 1) conf


------------------------------------------------------------------------
-- Exploration
------------------------------------------------------------------------

-- Generation -------------------------------------------------------------

data Generator g = Generator
  { initG          :: g
  , genTransitions :: g -> Int -> Config -> [((State, Symbol, Dir), g)]
      -- Called when we need a new transition
  }

data GenSt = GenSt
  { oldStates       :: [(State, Int)] -- number of open transitions in each old state
  , newStates       :: [State]
  , openTransitions :: Int
  , rGraph          :: ReachGraph State
  , curRules        :: Machine
  }
  deriving (Show)

smartGenerator :: Int -> Generator GenSt
smartGenerator n = Generator{..}
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
      -- guard $ or [ n >= lo
      --            , s' /= H
      --            , openTransitions == 1
      --            ]
      -- Make sure every closed state can reach an exit state
      guard $ and [ not $ Set.disjoint rs exitStates
                  | (s, 0) <- old'
                  , let rs = fromMaybe mempty $ Map.lookup s rg'
                  ]
      o <- if s' == H then [0] else [0, 1]
      d <- if s' == H then [L] else [L, R]

      -- (A, O) :-> (s, O, L) is never good, just make s the starting state!
      -- Not technically true, if you have a (s, O) :-> (A, O, L) transition you can
      -- buy an extra step by making s the starting state. But we can do that in a
      -- postprocessing step.
      guard $ (s, i, o, d) /= (A, 0, 0, L)

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
              [(0, o1), (1, o2)] -> Just (s, o1, o2)
              _                  -> Nothing
    (s, o1, o2) =~ (s', o1', o2') = eq o1 o1' && eq o2 o2'
      where
        eq o o' = r o == r o'
        r (s0, o, d)
          | s0 == s || s0 == s' = (Nothing, o, d) -- self transition
          | otherwise           = (Just s0, o, d)

-- Loop detection ---------------------------------------------------------

data LoopDetector l s = LoopDetector
  { emptyL   :: l                -- For an empty machine
  , stepL    :: l -> Rule -> l   -- When adding a new rule
  , initLs   :: s
  , stepLoop :: l -> s -> Int -> Config -> Config -> Either Reason s
  }

data LoopAnalysis = LoopAnalysis
  { leftStuck    :: [(State, Symbol)]
  , runners      :: [State]
  }
  deriving Show

loopAnalysis :: Machine -> LoopAnalysis
loopAnalysis m = LoopAnalysis
  { leftStuck = go [ ((s1, i), (s2, o)) | (s1, i) :-> (s2, o, L) <- m, s2 /= H ]
  , runners   = go [ (s, s') | (s, 0) :-> (s', _, R) <- m, s' /= H ]
  }
  where
    go :: Eq a => [(a, a)] -> [a]
    go g
      | g == g'   = is
      | otherwise = go g'
      where
        is  = map fst g
        g'  = [ e | e@(_, o) <- g, elem o is ]

loopCheck :: LoopAnalysis -> Int -> Config -> Config -> Maybe Reason
loopCheck loop _ _ (s, tape@(Tape NilC _ _))
  | elem (s, look tape) (leftStuck loop) = Just StuckLeft
-- loopCheck loop _ _ (s, Tape _ _ NilR)
--   | elem s (runners loop) = Just RunAway
-- loopCheck _ n _ (s, Tape w _ _)
--   | n > 100, w * 6 > n = Just TooWide
loopCheck _ _ _ _ = Nothing

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
        shouldCache = n < 25
        seen' | shouldCache = Set.insert conf seen
              | otherwise   = seen

-- Exploration ------------------------------------------------------------

runExplore :: Int -> Int -> [(Result, MacroMachine)]
runExplore n fuel = go fuel 0 0 initG emptyL initLs [] mempty initialConfig
  where
    Generator{..} = smartGenerator n
    LoopDetector{..} = loopDetector
    go fuel n k _ _ _ _ m _ | fuel <= 0 = pure (NoTermination OutOfFuel k, m)
    go fuel n k _ _ _ _ m (H, _) = pure (Terminated n k, m)
    go fuel !n k g l ls lastRule m conf@(s, tape) =
      case combineStep lastRule m conf of
        Nothing -> do
          -- Make up new rule
          (sod, g') <- genTransitions g n conf
          let rule = (s, look tape) :-> sod
              rs   = batchRule s $ basicRule rule
              l'   = stepL l rule
          go fuel n k g' l' ls lastRule (foldr (addRule s) m rs) conf
        Just (w, lastRule, m, conf') ->
          case stepLoop l ls n conf conf' of
            Left err  -> pure (NoTermination err k, m)
            Right ls' -> go (fuel - w) (n + w) (k + 1) g l ls' lastRule m conf'

exploreIO :: Int -> Int -> IO (Result, MacroMachine)
exploreIO n fuel = go 0 0 (Terminated 0 0, mempty) $ runExplore n fuel
  where
    go best worst mbest [] = pure mbest
    go best worst mbest ((r@(Terminated n k), m') : rs) = do
      let (best', mbest') | n > best  = (n, (r, m'))
                          | otherwise = (best, mbest)
      when (best' > best) $ printf "GOOD %3d %-9d: %s\n" k n (show $ toPrim m')
      let worst' = max k worst
      when (worst' > worst) $ printf "BAD  %3d %-9s: %s\n" k ("Halt" :: String) (show $ toPrim m')
      go best' worst' mbest' rs
    go best worst mbest ((r@(NoTermination err k), m') : rs) = do
      let worst' = max k worst
      when (worst' > worst) $ printf "BAD  %3d %-9s: %s\n" k (show err) (show $ toPrim m')
      go best worst' mbest rs

------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------

instance Pretty MacroClause where
  pPrint (i :=> o) = hsep [ pPrint i, "=>", pPrint o ]
  pPrint (BatchR i rp ls o) = hsep [ pPrint i, pPrintPrec prettyNormal 2 rp <> "ⁿ", "=>"
                                   , pPrintPrec prettyNormal 2 (CList.reverse ls) <> "ⁿ", pPrint o ]
  pPrint (BatchL lp i o rs) = hsep [ pPrintPrec prettyNormal 2 (CList.reverse lp) <> "ⁿ", pPrint i, "=>"
                                   , pPrint o, pPrintPrec prettyNormal 2 rs <> "ⁿ" ]

instance Pretty MacroRule where
  pPrint (Rule c s w) = (pPrint c <> ",") <+> text (printf "%s (cost %d)" (show s) w)

instance Pretty MacroMachine where
  pPrint (MacroMachine m) = vcat [ (pPrint s <> ":") <+> vcat (map pPrint rs) | (s, rs) <- Map.toList m ]

------------------------------------------------------------------------
-- QuickCheck properties
------------------------------------------------------------------------

instance Arbitrary MacroClause where
  arbitrary = (:=>) <$> genLHS <*> genRHS
    where
      genLHS = genPat
      genRHS = (,) <$> genPat <*> arbitrary
      genPat = Tape <$> short <*> arbitrary <*> short
      short = CList.fromList <$> do
        n <- choose (0, 3)
        vectorOf n arbitrary
  shrink (lhs :=> rhs) = [ lhs :=> rhs | (lhs, rhs) <- shrink (lhs, rhs) ]
  shrink (BatchR lhs rp ls rhs) =
    [ lhs :=> (rhs, R)
    , lhs :=> (rhs, L) ] ++
    [ BatchR lhs rp ls rhs | (lhs, rp, ls, rhs) <- shrink (lhs, rp, ls, rhs) ]
  shrink (BatchL lp lhs rhs rs) =
    [ lhs :=> (rhs, R)
    , lhs :=> (rhs, L) ] ++
    [ BatchL lp lhs rhs rs | (lp, lhs, rhs, rs) <- shrink (lp, lhs, rhs, rs) ]

instance Arbitrary MacroRule where
  arbitrary = Rule <$> arbitrary <*> arbitrary <*> choose (1, 10)
  shrink (Rule c s w) =
    [ Rule c s w | (c, s, w) <- shrink (c, s, w), w > 0 ]

prop_combine :: MacroRule -> MacroRule -> Property
prop_combine r1 r2 =
  case combineRules r1 r2 of
    Nothing -> discard
    Just (Rule BatchR{} _ _) -> error "impossible"
    Just (Rule BatchL{} _ _) -> error "impossible"
    Just r3@(Rule (lhs :=> _) _ _) ->
      counterexampleD [ "r1 =" <+> pPrint r1
                      , "r2 =" <+> pPrint r2
                      , "r3 =" <+> pPrint r3
                      , "---"
                      , "init:" <+> pPrint conf
                      , "r3 ->" <+> pPrint (apply r3 conf)
                      , "r1 ->" <+> pPrint (apply r1 conf)
                      , "r2 ->" <+> pPrint (apply r2 =<< apply r1 conf)
                      ] $
      apply r3 conf === (apply r2 =<< apply r1 conf)
      where conf = (A, lhs)
  where
    apply r conf = do (_, _, conf) <- macroRule r conf; pure conf

prop_batch :: NonNegative Int -> MacroRule -> Property
prop_batch (NonNegative n) r@(Rule _ s _) = case batchRule s r of
  b@(Rule (BatchR (Tape lp x rp) rp₂ _ _) _ w) : _ ->
    counterexampleD [ "r =" <+> pPrint r
                    , "b =" <+> pPrint b
                    , "tape =" <+> pPrint tape
                    , "run r^n:" <+> pPrint expect
                    , "run b:  " <+> pPrint actual ] $
      conjoin [ counterexample "empty repeat!" $ not $ null rp₂
              , actual === expect ]
    where
      tape = Tape lp x (rp <> CList.concatReplicate n rp₂)
      expect = foldM apply (A, tape) $ replicate (n + 1) r
      actual = apply (A, tape) b
      apply conf r = do (_, _, conf) <- macroRule r conf; pure conf
  b@(Rule (BatchL lp₂ (Tape lp x rp) _ _) _ w) : _ ->
    counterexampleD [ "r =" <+> pPrint r
                    , "b =" <+> pPrint b
                    , "tape =" <+> pPrint tape
                    , "run r^n:" <+> pPrint expect
                    , "run b:  " <+> pPrint actual ] $
      conjoin [ counterexample "empty repeat!" $ not $ null lp₂
              , actual === expect ]
    where
      tape = Tape (CList.concatReplicate n lp₂ <> lp) x rp
      expect = foldM apply (A, tape) $ replicate (n + 1) r
      actual = apply (A, tape) b
      apply conf r = do (_, _, conf) <- macroRule r conf; pure conf
  _ -> discard

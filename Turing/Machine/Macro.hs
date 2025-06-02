
module Turing.Machine.Macro where

import Control.Applicative
import Control.Monad
import Control.Concurrent
import Data.Foldable
import Data.List (nub, sort)
import Data.List.Compressed qualified as CList
import Data.List.Compressed (CList, pattern NilC, pattern (:@))
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Maybe
import Data.ReachGraph
import System.Timeout.Unsafe
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
data Wall = YesWall | AnyWall
  deriving (Eq, Ord, Show)

data MacroClause = Clause Wall LHS RHS Dir
                 | BatchL (CList Symbol) (CList Symbol) LHS RHS (CList Symbol) (CList Symbol) Int
                 | BatchR LHS (CList Symbol) (CList Symbol) (CList Symbol) (CList Symbol) RHS Int
  deriving (Eq, Ord, Show)
data MacroRule = Rule MacroClause State Int
  deriving (Eq, Ord, Show)

data MacroRules = MacroRules
  { batchedRules :: [MacroRule]
  , normalRules  :: [MacroRule]
  }
  deriving Show

instance Semigroup MacroRules where
  MacroRules b n <> MacroRules b' n' = MacroRules (b ++ b') (n ++ n')

instance Monoid MacroRules where
  mempty = MacroRules [] []

singleMacroRule :: MacroRule -> MacroRules
singleMacroRule r@(Rule c _ _) = case c of
  Clause{} -> MacroRules [] [r]
  BatchL{} -> MacroRules [r] []
  BatchR{} -> MacroRules [r] []

zipMacroRules :: ([MacroRule] -> [MacroRule] -> [MacroRule])
               -> MacroRules -> MacroRules -> MacroRules
zipMacroRules f (MacroRules b r) (MacroRules b' r') = MacroRules (f b b') (f r r')

newtype MacroMachine = MacroMachine (Map State MacroRules)
  deriving Show

rules :: MacroMachine -> State -> MacroRules
rules (MacroMachine m) s = fromMaybe mempty $ Map.lookup s m

allRules :: MacroMachine -> State -> [MacroRule]
allRules m s = b ++ r
  where MacroRules b r = rules m s

addRule :: State -> MacroRule -> MacroMachine -> MacroMachine
addRule s r (MacroMachine m) = MacroMachine $
    Map.insertWith (zipMacroRules ins) s (singleMacroRule r) m
  where
    ins [] rs = rs
    ins rs1 rs2 = rs1 ++ filter (not . subsumed) rs2
      where subsumed r = any (`subsumes` r) rs1
    subsumes (Rule (Clause w lhs _ _) _ _) (Rule (Clause w' lhs' _ _) _ _) = (w, lhs) == (w', lhs')
    subsumes (Rule (BatchR lhs rp rt _ _ _ _) _ _) (Rule (BatchR lhs' rp' rt' _ _ _ _) _ _) = (lhs, rp, rt) == (lhs', rp', rt')
    subsumes (Rule (BatchL lt lp lhs _ _ _ _) _ _) (Rule (BatchL lt' lp' lhs' _ _ _ _) _ _) = (lt, lp, lhs) == (lt', lp', lhs')
    subsumes _ _ = False

ruleCost :: MacroRule -> Int
ruleCost (Rule _ _ w) = w

-- instance Semigroup Wall where
--   AnyWall <> w = w
--   w <> AnyWall = w
--   YesWall <> _ = YesWall
--   _ <> YesWall = YesWall
--   NoWall <> NoWall = NoWall

instance Semigroup MacroMachine where
  MacroMachine m <> MacroMachine m' = MacroMachine $ Map.unionWith (<>) m m'

instance Monoid MacroMachine where
  mempty = MacroMachine mempty

------------------------------------------------------------------------
-- Building macro rules
------------------------------------------------------------------------

basicRule :: Rule -> MacroRule
basicRule ((_, i) :-> (s', o, d)) =
  Rule (Clause AnyWall (Tape mempty i mempty) (Tape mempty o mempty) d) s' 1

fromPrimRule :: Rule -> MacroMachine
fromPrimRule r@((s, _) :-> (s', o, d)) =
  MacroMachine $ Map.singleton s
               $ mconcat
               $ map singleMacroRule
               $ batchRule s mr
  where
    mr = basicRule r

fromPrim :: Machine -> MacroMachine
fromPrim = foldMap fromPrimRule

toPrim :: MacroMachine -> Machine
toPrim (MacroMachine m) =
  [ (s, i) :-> (s', o, d)
  | (s, MacroRules{..}) <- Map.toList m
  , Rule (Clause w (Tape NilC i NilC) (Tape NilC o NilC) d) s' 1 <- normalRules
  , w /= YesWall ]

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

combineRules :: MacroRule -> MacroRule -> [MacroRule]
combineRules r₁ r₂ = do
  r <- combineRules' r₁ r₂
  guard $ not $ tooBig r
  pure r
  where
    tooBig (Rule (Clause _ (Tape l _ r) _ _) _ _) = CList.length l + CList.length r > 11
    tooBig _ = False

combineRules' :: MacroRule -> MacroRule -> [MacroRule]
combineRules' r₁@(Rule c₁ _ w₁) r₂@(Rule c₂ s₂ w₂) = do
  (w, c) <- combineClauses c₁ c₂
  let r = Rule c s₂ (w + w₁ + w₂)
  -- trace (show $ nest 2 $ vcat
  --               [ "+" <+> pPrint r₁
  --               , "+" <+> pPrint r₂
  --               , "=" <+> pPrint r ]) $
  pure r

infix 1 ===>
(===>) :: Bool -> Bool -> Bool
True  ===> x = x
False ===> _ = True

-- Int is extra cost that needs to be pushed up. Happens when combining batch rules and
-- the first rule produces output consumed by the batch part of the second rule.
combineClauses :: MacroClause -> MacroClause -> [(Int, MacroClause)]
combineClauses (Clause YesWall (Tape lp₁ i₁ rp₁) (move L -> Tape ls₁ o₁ rs₁) L)
               (Clause w (Tape lp₂ i₂ rp₂) (Tape ls₂ o₂ rs₂) d₂) = maybeToList $ do
  guard $ o₁ == i₂
  (lp, ls) <- CList.dropEitherPrefix lp₂ ls₁
  guard $ w == YesWall ===> (lp, ls) == (NilC, NilC)
  (rp, rs) <- CList.dropEitherPrefix rp₂ rs₁
  -- () <- traceM $ show $ "(lp, ls) =" <+> pPrint (lp, ls)
  pure (0, Clause YesWall (Tape (lp₁ <> lp) i₁ (rp₁ <> rp)) (Tape (ls₂ <> ls) o₂ (rs₂ <> rs)) d₂)
combineClauses (Clause w₁ lhs₁ rhs₁ d₁) (Clause w₂ lhs₂ rhs₂ d₂) = maybeToList $ do
  c@((lp₁, rp₁), (ls₂, rs₂)) <- chainMatch lhs₂ rhs₁ d₁
  -- () <- traceM $ show $ pPrint c
  let lhs@(Tape lp _ rp) = plugLHS lp₁ lhs₁ rp₁
      rhs = plugRHS ls₂ rhs₂ rs₂
  -- () <- traceM $ show $ "lhs =" <+> pPrint lhs
  -- () <- traceM $ show $ "rhs =" <+> pPrint rhs
  guard $ w₁ == YesWall ===> lp₁ == NilC
  guard $ w₂ == YesWall ===> ls₂ == NilC
  let glb AnyWall w = pure w
      glb w AnyWall = pure w
      glb w₁ w₂     = w₁ <$ guard (w₁ == w₂)
  w <- if | (lp₁, ls₂) == (NilC, NilC) -> glb w₁ w₂
          | lp₁ == NilC                -> pure w₁
          | otherwise                  -> pure w₂
  pure (0, Clause w lhs rhs d₂)

combineClauses (Clause AnyWall lhs rhs d)
               (BatchR (Tape lp₂ i₂ rp₂) rrp₂ rt lt lls₂ (Tape ls₂ o₂ rs₂) k) = maybeToList $ do
  (Tape lp₁ i₁ rp₁, Tape ls₁ _ rs₁) <- alignOn i₂ lhs rhs d
  (lp, ls)  <- CList.dropEitherPrefix lp₂ ls₁
  (rp, rs)  <- CList.dropEitherPrefix rp₂ rs₁
  (NilC, j) <- pure $ CList.dropRepeatedPrefix rrp₂ rs
  pure (j * k,
        BatchR (Tape (lp₁ <> lp) i₁ (rp₁ <> rp)) rrp₂ rt
               (lt <> ls) lls₂ (Tape (ls₂ <> CList.concatReplicate j lls₂) o₂ rs₂) k)

combineClauses (Clause AnyWall lhs rhs d)
               (BatchL lt llp₂ (Tape lp₂ i₂ rp₂) (Tape ls₂ o₂ rs₂) rrs₂ rt k) = maybeToList $ do
  (Tape lp₁ i₁ rp₁, Tape ls₁ o₁ rs₁) <- alignOn i₂ lhs rhs d
  (lp, ls) <- CList.dropEitherPrefix lp₂ ls₁
  (rp, rs) <- CList.dropEitherPrefix rp₂ rs₁
  (NilC, j)  <- pure $ CList.dropRepeatedPrefix llp₂ ls
  pure (j * k,
        BatchL lt llp₂ (Tape (lp₁ <> lp) i₁ (rp₁ <> rp))
               (Tape ls₂ o₂ (rs₂ <> CList.concatReplicate j rrs₂)) rrs₂ (rt <> rs) k)

combineClauses _ _ = []

alignOn :: Symbol -> Tape -> Tape -> Dir -> Maybe (Tape, Tape)
alignOn x lhs rhs d
  | Just rhs' <- safeMove d rhs = (lhs, rhs') <$ guard (look rhs' == x)
alignOn x (Tape lp i rp) (Tape NilC o rs) L =
  pure (Tape (lp <> CList.fromList [x]) i rp, Tape NilC x (o :@ rs))
alignOn x (Tape lp i rp) (Tape ls o NilC) R =
  pure (Tape lp i (rp <> CList.fromList [x]), Tape (o :@ ls) x NilC)
alignOn _ _ _ _ = Nothing

safeMove :: Dir -> Tape -> Maybe Tape
safeMove L (Tape (x :@ l) y r) = pure $ Tape l x (y :@ r)
safeMove R (Tape l y (x :@ r)) = pure $ Tape (y :@ l) x r
safeMove _ _ = Nothing

-- Batching ---------------------------------------------------------------

batchRight :: LHS -> RHS -> Maybe (CList Symbol, CList Symbol)
batchRight (Tape lp x rp) (Tape ls y rs)
  | Just rp₂ <- CList.dropPrefix rs (x :@ rp)
  , Just ls₂ <- CList.dropPrefix lp (y :@ ls)
  , not $ null rp₂
  , not $ null ls₂ = Just (ls₂, rp₂)
batchRight _ _ = Nothing

batchLeft :: LHS -> RHS -> Maybe (CList Symbol, CList Symbol)
batchLeft (Tape lp x rp) (Tape ls y rs) = do
  (rs₂, lp₂) <- batchRight (Tape rp x lp) (Tape rs y ls)
  pure (lp₂, rs₂)

batchDir :: Dir -> LHS -> RHS -> Maybe (Int -> MacroClause)
batchDir L lhs rhs = do
  (lp, rs) <- batchLeft lhs rhs
  pure $ BatchL NilC lp lhs rhs rs NilC
batchDir R lhs rhs = do
  (ls, rp) <- batchRight lhs rhs
  pure $ BatchR lhs rp NilC NilC ls rhs

batchRule :: State -> MacroRule -> [MacroRule]
batchRule s rule@(Rule (Clause w lhs rhs R) s' k)
  | s == s'
  , w /= YesWall
  , Just (ls, rp) <- batchRight lhs rhs
  = [Rule (BatchR lhs rp NilC NilC ls rhs k) s k, rule]
batchRule s rule@(Rule (Clause w lhs rhs L) s' k)
  | w /= YesWall
  , s == s'
  , Just (lp, rs) <- batchLeft lhs rhs
  = [Rule (BatchL NilC lp lhs rhs rs NilC k) s k, rule]
batchRule s rule@(Rule (Clause w lhs rhs d) s' k)
  | w /= YesWall
  , s == s'
  , Just rhs' <- safeMove d =<< safeMove d rhs
  , Just cls  <- batchDir (op d) lhs rhs'
  = [Rule (cls k) s k, rule]
batchRule s rule
  | Just r <- unbatchRule 0 rule
  , r' : _ : _ <- batchRule s r
  , r' /= rule = [r', rule]
batchRule _ rule = [rule]

infixr 5 |>
(|>) :: CList Symbol -> Tape -> Tape
l' |> Tape l x r = Tape (l <> l') x r

infixl 5 <|
(<|) :: Tape -> CList Symbol -> Tape
Tape l x r <| r' = Tape l x (r <> r')

unbatchRule :: Int -> MacroRule -> Maybe MacroRule
unbatchRule n (Rule (BatchR lhs rp rt lt ls rhs j) s k) =
  pure $ Rule (Clause AnyWall (lhs <| CList.concatReplicate n rp <| rt)
                              (lt |> CList.concatReplicate n ls |> rhs) R) s (k + j * n)
unbatchRule n (Rule (BatchL lt lp lhs rhs rs rt j) s k) =
  pure $ Rule (Clause AnyWall (lt |> CList.concatReplicate n lp |> lhs)
                              (rhs <| CList.concatReplicate n rs <| rt) L) s (k + j * n)
unbatchRule _ _ = Nothing

-- Wall bounces -----------------------------------------------------------

wallBounceClause :: MacroClause -> MacroClause
wallBounceClause = \ case
  Clause AnyWall lhs (Tape (o :@ NilC) o' rs) L ->
    Clause YesWall lhs (Tape NilC o (o' :@ rs)) L
  Clause AnyWall lhs rhs@(Tape NilC _ _) L ->
    Clause YesWall lhs rhs L
  r -> r

wallBounceRule :: MacroRule -> MacroRule
wallBounceRule (Rule c s w) = Rule (wallBounceClause c) s w

------------------------------------------------------------------------
-- Running
------------------------------------------------------------------------

matchLHS :: LHS -> Tape -> Maybe (CList Symbol, CList Symbol)
matchLHS (Tape lp x rp) (Tape ls y rs)
  | x == y
  , Just ls' <- CList.dropPrefix lp ls
  , Just rs' <- CList.dropPrefix rp rs = pure (ls', rs')
matchLHS _ _ = Nothing

macroRule :: MacroRule -> Config -> Maybe (Int, Int, MacroRule, Config)
macroRule r (_, tape) = do
  (j, n, conf) <- match r tape
  pure (j, n, r, conf)
  where
    match (Rule (Clause wall lhs rhs d) s1 w) tape = do
      (ls, rs) <- matchLHS lhs tape
      guard $ case wall of
                YesWall -> ls == NilC
                AnyWall -> True
      pure (1, w, (s1, move d $ plugRHS ls rhs rs))

    match rule@(Rule (BatchR (Tape lp x rp) rp₂ rt lt ls₂ (Tape ls y rs) k) s1 w) tape@(Tape l z r) = do
      guard $ x == z
      l₁ <- CList.dropPrefix lp l
      r₁ <- CList.dropPrefix rp r
      let (r₂, n) = CList.dropRepeatedPrefix rp₂ r₁
      r₂' <- CList.dropPrefix rt r₂
      guard $ n > 3
      let result = move R $ Tape (ls <> CList.concatReplicate n ls₂ <> lt <> l₁) y (rs <> r₂')
      pure (n, n * k + w, (s1, result))

    match rule@(Rule (BatchL lt lp₂ (Tape lp x rp) (Tape ls y rs) rs₂ rt k) s1 w) tape@(Tape l z r) = do
      guard $ x == z
      l₁ <- CList.dropPrefix lp l
      r₁ <- CList.dropPrefix rp r
      let (l₂, n) = CList.dropRepeatedPrefix lp₂ l₁
      l₂' <- CList.dropPrefix lt l₂
      guard $ n > 3
      let result = move L $ Tape (ls <> l₂') y (rs <> CList.concatReplicate n rs₂ <> rt <> r₁)
      pure (n, n * k + w, (s1, result))

macroStep :: MacroMachine -> Config -> Maybe (Int, Int, MacroRule, Config)
macroStep m conf@(s, _) = foldr (<|>) Nothing [ macroRule r conf | r <- allRules m s ]

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

combineStep :: Bool
            -> LastRules
            -> MacroMachine
            -> Config
            -> Maybe (Int, LastRules, MacroMachine, Config)
combineStep verbose lastRules m conf@(s, Tape l _ _) =
  case macroStep m conf of
    Nothing            -> Nothing
    Just (j, w, rUsed, conf') ->
      dbg $ Just (w, lastRules', m', conf')
      where
        dbg | verbose   = trace $ "\ESC[37m" ++ show (nest 8 $ pPrint r) ++ "\ESC[0m"
            | otherwise = id
        r | isWall    = wallBounceRule rUsed
          | otherwise = rUsed
        urs = maybeToList $ unbatchRule j r
        newRules = do
          (s0, r0) <- lastRules
          [ (s0, r') | r' <- concatMap (combine s0 r0) (r : urs) ]
        m' = foldr addNew m newRules
        lastRules' = (s, r) : newRules
        primM = toPrim m
        combine s0 r1 r2 = map (validate s0 r1 r2) rs
          where
            rs = combineRules r1 r2
        validate s r1 r2 r
          | verbose, Just tape <- failCombine =
              error $ show $ vcat
                [ "Failed combine"
                , nest 2 $ "r1   =" <+> pPrint r1
                , nest 2 $ "r2   =" <+> pPrint r2
                , nest 2 $ "r    =" <+> pPrint r
                , nest 2 $ "tape =" <+> pPrint tape
                , nest 2 $ "r1    ->" <+> pPrint (app r1 (0, (s, tape)))
                , nest 2 $ "r1;r2 ->" <+> pPrint (app r2 =<< app r1 (0, (s, tape)))
                , nest 2 $ "r     ->" <+> pPrint (app r (0, (s, tape)))
                ]
          | verbose, not $ validateRule primM s r =
              error $ show $ vcat
                [ "Failed to validate rule"
                , nest 2 $ "r1 =" <+> pPrint r1
                , nest 2 $ "r2 =" <+> pPrint r2
                , nest 2 $ "r  =" <+> pPrint r
                , nest 2 $ "prim =" <+> pPrint primM ]
          | otherwise = r
          where
            app r (n, conf) = do
              (_, m, _, conf) <- macroRule r conf
              pure (n + m, conf)
            failCombine = listToMaybe
              [ tape | tape <- validationTapes r,
                       (app r2 =<< app r1 (0, (s, tape)))
                        /=
                       app r (0, (s, tape)) ]
        addNew (s0, r') m = foldr (addRule s0) m (batchRule s0 r')
  where
    isWall = l == NilC

macroRun' :: Bool -> Int -> MacroMachine -> (Result, MacroMachine)
macroRun' verbose fuel m0 = goV m0 [] fuel 0 0 initialConfig
  where
    goV m lastRules fuel n k conf@(s, tape) = dbg $ go m lastRules fuel n k conf
      where
        dbg | verbose   = trace $ printf "%7d %3d | %s: %s" n k (show s) (show $ pPrint tape)
            | otherwise = id

    go m _ fuel _ k _ | fuel <= 0 = (NoTermination OutOfFuel k, m)
    go m _ _ n k (H, _) = (Terminated n k, m)
    go m lastRules fuel !n !k conf@(s, _) =
      case combineStep verbose lastRules m conf of
        Nothing                      -> error $ show $ "step failed on" <+> pPrint conf
        Just (w, lastRules, m, conf) -> goV m lastRules (fuel - w) (n + w) (k + 1) conf

-- Checking rules ---------------------------------------------------------

validationTapes :: MacroRule -> [Tape]
validationTapes (Rule c _ _) = case c of
  Clause w lhs _ _ -> [ l |> (lhs <| r) | l <- lpaddings w, r <- rpaddings ]
  BatchL lt lp lhs _ _ _ _ ->
    [ l |> lt |> CList.concatReplicate 4 lp |> (lhs <| r)
    | l <- lpaddings AnyWall, r <- rpaddings ]
  BatchR lhs rp rt _ _ _ _ ->
    [ (l |> lhs) <| CList.concatReplicate 4 rp <| rt <| r
    | l <- lpaddings AnyWall, r <- rpaddings ]
  where
    rpaddings = map CList.fromList [[], [1], [1, 1]]
    lpaddings YesWall = [NilC]
    lpaddings AnyWall = map CList.fromList $ [] : [ x : xs | x <- [0, 1], xs <- [[], [0], [1]] ]

validateRule :: Machine -> State -> MacroRule -> Bool
validateRule m s r = all validate $ validationTapes r
  where
    validate tape = Just True == do
      (_, n₁, _, conf₁) <- macroRule r (s, tape)
      let (n₂, conf₂) = primRun' False n₁ m (s, tape)
          ok = (n₁, conf₁) == (n₂, conf₂)
      unless ok $ do
        () <- traceM $ show $ vcat
                [ "conf =" <+> pPrint (s, tape)
                , "rule ->" <+> pPrint (n₁, conf₁)
                , "prim ->" <+> pPrint (n₂, conf₂)
                ]
        let !_ = primRun' True n₁ m (s, tape)
        pure ()
      pure ok

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
    go fuel !n k g l ls lastRules m conf@(s, tape) =
      case combineStep False lastRules m conf of
        Nothing -> do
          -- Make up new rule
          (sod, g') <- genTransitions g n conf
          let isWall = case tape of Tape l _ _ -> l == NilC
              rule = (s, look tape) :-> sod
              basic = basicRule rule
              rs   = batchRule s basic ++ [wallBounceRule basic | isWall]
              l'   = stepL l rule
          go fuel n k g' l' ls lastRules (foldr (addRule s) m rs) conf
        Just (w, lastRules, m, conf') ->
          case stepLoop l ls k conf conf' of
            Left err  -> pure (NoTermination err k, m)
            Right ls' -> go (fuel - w) (n + w) (k + 1) g l ls' lastRules m conf'

data Stats = Stats { statResults :: !(Map String Int)
                   , totalSteps  :: !Int
                   }

noStats :: Stats
noStats = Stats mempty 0

addResult :: String -> Stats -> Stats
addResult r (Stats m n) = Stats (Map.insertWith (+) r 1 m) n

addSteps :: Int -> Stats -> Stats
addSteps k (Stats m n) = Stats m (n + k)

printStats :: Stats -> IO ()
printStats Stats{..} = do
  let total = sum statResults
      frac n = fromIntegral @_ @Double n / fromIntegral total
  sequence_ [ printf "--  %-10s %9d  (%4.1f%%)\n" r n (100 * frac n)
            | (r, n) <- Map.toList statResults ]
  printf "--  %-10s %9d\n" ("Total" :: String) total
  printf "--  Average steps: %.1f\n" (frac totalSteps)
  printf "--  Max steps:     %d\n" (0 :: Int)
  printf "--  Time:          %.1fs\n" (0.0 :: Double)

exploreIO :: Int -> Int -> IO ((Result, MacroMachine), Stats)
exploreIO n fuel = go noStats 0 0 (Terminated 0 0, mempty) $ runExplore n fuel
  where
    go stats best worst mbest [] = pure (mbest, stats)
    go !stats best worst mbest ((r@(Terminated n k), m') : rs) = do
      let (best', mbest') | n > best  = (n, (r, m'))
                          | otherwise = (best, mbest)
      when (best' > best) $ printf "GOOD %4d %-9d: %s\n" k n (show $ toPrim m')
      let worst' = max k worst
      when (worst' > worst) $ printf "BAD  %4d %-9s: %s\n" k ("Halt" :: String) (show $ toPrim m')
      let stats' = addSteps k $ addResult "Terminated" stats
      go stats' best' worst' mbest' rs
    go !stats best worst mbest ((r@(NoTermination err k), m') : rs) = do
      let worst' = max k worst
      when (worst' > worst) $ printf "BAD  %4d %-9s: %s\n" k (show err) (show $ toPrim m')
      let stats' = addSteps k $ addResult (show err) stats
      go stats' best worst' mbest rs

------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------

instance Pretty MacroClause where
  pPrint (Clause w lhs rhs d) = hsep [ pw, pPrint lhs, "=>", pPrint rhs, pPrint d ]
    where pw | w == YesWall = "|"
             | otherwise    = Text.Pretty.empty
  pPrint (BatchR i rp rt lt ls o k) =
    hsep [ pPrint i, pPrintPrec prettyNormal 2 rp <> "ⁿ", pPrint rt, "=>"
         , pPrint (CList.reverse lt), pPrintPrec prettyNormal 2 (CList.reverse ls) <> "ⁿ", pPrint o
         , parens $ text $ printf "cost n×%d" k ]
  pPrint (BatchL lt lp i o rs rt k) =
    hsep [ pPrint (CList.reverse lt), pPrintPrec prettyNormal 2 (CList.reverse lp) <> "ⁿ", pPrint i, "=>"
         , pPrint o, pPrintPrec prettyNormal 2 rs <> "ⁿ", pPrint rt
         , parens $ text $ printf "cost n×%d" k ]

instance Pretty MacroRule where
  pPrint (Rule c s w) = (pPrint c <> ",") <+> text (printf "%s (cost %d)" (show s) w)

instance Pretty MacroMachine where
  pPrint (MacroMachine m) = vcat [ (pPrint s <> ":") <+> vcat (map pPrint $ b ++ r)
                                 | (s, MacroRules b r) <- Map.toList m ]

------------------------------------------------------------------------
-- QuickCheck properties
------------------------------------------------------------------------

instance Arbitrary Wall where
  arbitrary = elements [YesWall, AnyWall]
  shrink _ = []

instance Arbitrary MacroClause where
  arbitrary = Clause <$> arbitrary <*> genLHS <*> genPat <*> arbitrary
    where
      genLHS = genPat
      genPat = Tape <$> short <*> arbitrary <*> short
      short = CList.fromList <$> do
        n <- choose (0, 3)
        vectorOf n arbitrary
  shrink (Clause w lhs rhs d) = [ Clause w lhs rhs d | (w, lhs, rhs, d) <- shrink (w, lhs, rhs, d) ]
  shrink (BatchR lhs rp rt lt ls rhs k) =
    [ Clause AnyWall lhs rhs R
    , Clause AnyWall lhs rhs L ] ++
    [ BatchR lhs rp rt lt ls rhs k
    | (lhs, rp, rt, lt, ls, rhs) <- shrink (lhs, rp, rt, lt, ls, rhs)
    , not $ null rp
    , not $ null ls ]
  shrink (BatchL lt lp lhs rhs rs rt k) =
    [ Clause AnyWall lhs rhs R
    , Clause AnyWall lhs rhs L ] ++
    [ BatchL lt lp lhs rhs rs rt k
    | (lt, lp, lhs, rhs, rs, rt) <- shrink (lt, lp, lhs, rhs, rs, rt)
    , not $ null lp
    , not $ null rs ]

instance Arbitrary MacroRule where
  arbitrary = Rule <$> arbitrary <*> arbitrary <*> choose (1, 10)
  shrink (Rule c s w) =
    [ Rule c s w | (c, s, w) <- shrink (c, s, w), w > 0 ]

genSmallTape :: Gen Tape
genSmallTape = Tape <$> syms <*> arbitrary <*> syms
  where
    syms = CList.fromList <$> frequency
      [ (3, pure [])
      , (2, vectorOf 1 arbitrary)
      , (1, vectorOf 2 arbitrary)
      , (1, vectorOf 3 arbitrary)
      ]

genMatchingRule :: Tape -> Gen MacroRule
genMatchingRule (Tape l x r) = do
  nl <- choose (0, CList.length l)
  nr <- choose (0, CList.length r)
  let tk n = CList.fromList . take n . toList
  rhs <- genSmallTape
  (d, s, k) <- arbitrary
  let oob = case (d, rhs) of
              (L, Tape NilC _ _) -> True
              _                  -> False
  w <- if | nl == CList.length l -> pure YesWall
          | otherwise            -> pure AnyWall
  pure $ Rule (Clause w (Tape (tk nl l) x (tk nr r)) rhs d) s k

shrinkMatchingRule :: Tape -> MacroRule -> [MacroRule]
shrinkMatchingRule tape r = [ r | r <- shrink r, isJust (macroRule r (A, tape)) ]

prop_matchingRule :: Tape -> Property
prop_matchingRule tape = forAll (genMatchingRule tape) $ \ r ->
  counterexampleD [ "tape =" <+> pPrint tape
                  , "r =" <+> pPrint r] $
  isJust (macroRule r (A, tape))

-- prop_combine :: MacroRule -> MacroRule -> Property
-- prop_combine r1 r2 =
prop_combine :: Property
prop_combine =
  forAllShrink genSmallTape shrink $ \ tape ->
  forAllShrink (genMatchingRule tape) (shrinkMatchingRule tape) $ \ r1 ->
  let (_, tape') = fromMaybe discard $ apply r1 (A, tape) in
  forAllShrink (genMatchingRule tape') (shrinkMatchingRule tape') $ \ r2 ->
  case combineRules' r1 r2 of
    [] ->
      counterexampleD [ "r1 =" <+> pPrint r1
                      , "r2 =" <+> pPrint r2
                      , "r3 = Nothing"
                      , "---"
                      , "init:" <+> pPrint conf
                      , "r1 ->" <+> pPrint (fmap snd $ apply r1 conf)
                      , "r2 ->" <+> pPrint (fmap snd $ apply r2 =<< apply r1 conf)
                      ] False
      where conf = (A, tape)
    rs ->
      conjoin $ do
      r3 <- rs
      let Rule (Clause _ lhs _ _) _ _ = r3
          conf = (A, lhs)
      pure $
        counterexampleD [ "r1 =" <+> pPrint r1
                        , "r2 =" <+> pPrint r2
                        , "r3 =" <+> pPrint r3
                        , "---"
                        , "init:" <+> pPrint conf
                        , "r1 ->" <+> pPrint (apply r1 conf)
                        , "r2 ->" <+> pPrint (apply r2 =<< apply r1 conf)
                        , "r3 ->" <+> pPrint (apply r3 conf)
                        ] $
        apply r3 conf === (apply r2 =<< apply r1 conf)
  where
    apply r conf = do (_, _, _, conf) <- macroRule r conf; pure conf

prop_batch :: NonNegative Int -> MacroRule -> Property
prop_batch (NonNegative ((+ 4) -> n)) r@(Rule _ s _) = case batchRule s r of
  b@(Rule (BatchR (Tape lp x rp) rp₂ rt _ _ _ _) _ w) : _ ->
    counterexampleD [ "r =" <+> pPrint r
                    , "b =" <+> pPrint b
                    , "tape =" <+> pPrint tape
                    , "run r^n:" <+> pPrint expect
                    , "run b:  " <+> pPrint actual ] $
      conjoin [ counterexample "empty repeat!" $ not $ null rp₂
              , actual === expect ]
    where
      tape = Tape lp x (rp <> CList.concatReplicate n rp₂ <> rt)
      expect = foldM apply (A, tape) $ replicate (n + 1) r
      actual = apply (A, tape) b
      apply conf r = do (_, _, _, conf) <- macroRule r conf; pure conf
  b@(Rule (BatchL lt lp₂ (Tape lp x rp) _ _ _ _) _ w) : _ ->
    counterexampleD [ "r =" <+> pPrint r
                    , "b =" <+> pPrint b
                    , "tape =" <+> pPrint tape
                    , "run r^n:" <+> pPrint expect
                    , "run b:  " <+> pPrint actual ] $
      conjoin [ counterexample "empty repeat!" $ not $ null lp₂
              , actual === expect ]
    where
      tape = Tape (lp <> CList.concatReplicate n lp₂ <> lt) x rp
      expect = foldM apply (A, tape) $ replicate (n + 1) r
      actual = apply (A, tape) b
      apply conf r = do (_, _, _, conf) <- macroRule r conf; pure conf
  _ -> discard

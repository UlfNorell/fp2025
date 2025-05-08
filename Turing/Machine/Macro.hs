
module Turing.Machine.Macro where

import Control.Applicative
import Control.Monad
import Data.List.Compressed qualified as CList
import Data.List.Compressed (CList, pattern NilC, pattern (:@))
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe
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

basicRule :: Rule -> MacroMachine
basicRule ((s, i) :-> (s', o, d)) = MacroMachine $
  Map.singleton s [Rule (Tape mempty i mempty :=> (Tape mempty o mempty, d)) s' 1]

fromPrim :: Machine -> MacroMachine
fromPrim = foldMap basicRule

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

batchRule :: State -> MacroRule -> MacroRule
batchRule s rule@(Rule (lhs :=> (rhs, R)) s' w)
  | s == s'
  , Just (ls, rp) <- batchRight lhs rhs
  , not $ null rp = Rule (BatchR lhs rp ls rhs) s w
    -- trace (show $ vcat [ "rule: " <+> pPrint rule
    --                    , "batch:" <+> pPrint brule ]) brule
batchRule s rule@(Rule (lhs :=> (rhs, L)) s' w)
  | s == s'
  , Just (lp, rs) <- batchLeft lhs rhs
  , not $ null lp = Rule (BatchL lp lhs rhs rs) s w
batchRule _ r = r

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
      -- trace (show $ vcat [ "applying" <+> pPrint rule
      --                    , "      to" <+> pPrint tape
      --                    , "ls  =" <+> pPrint ls
      --                    , "ls₂ =" <+> pPrint ls₂
      --                    , "n   =" <+> pPrint n
      --                    , "r₂  =" <+> pPrint r₂
      --                    , "concatRep  =" <+> pPrint (CList.concatReplicate n ls₂)
      --                    , "l₁  =" <+> pPrint l₁
      --                    , "rt  =" <+> pPrint (rs <> r₂)
      --                    ]) $ do
      let result = move R $ Tape (ls <> CList.concatReplicate n ls₂ <> l₁) y (rs <> r₂)
        -- trace (show $ "  result" <+> pPrint result) $
      pure ((n + 1) * w, (s1, result))
    match rule@(Rule (BatchL lp₂ (Tape lp x rp) (Tape ls y rs) rs₂) s1 w) tape@(Tape l z r) = do
      guard $ x == z
      l₁ <- CList.dropPrefix lp l
      r₁ <- CList.dropPrefix rp r
      let (l₂, n) = CList.dropRepeatedPrefix lp₂ l₁
      -- trace (show $ vcat [ "applying" <+> pPrint rule
      --                    , "      to" <+> pPrint tape
      --                    , "ls  =" <+> pPrint ls
      --                    , "ls₂ =" <+> pPrint ls₂
      --                    , "n   =" <+> pPrint n
      --                    , "r₂  =" <+> pPrint r₂
      --                    , "concatRep  =" <+> pPrint (CList.concatReplicate n ls₂)
      --                    , "l₁  =" <+> pPrint l₁
      --                    , "rt  =" <+> pPrint (rs <> r₂)
      --                    ]) $ do
      let result = move L $ Tape (ls <> l₂) y (rs <> CList.concatReplicate n rs₂ <> r₁)
        -- trace (show $ "  result" <+> pPrint result) $
      pure ((n + 1) * w, (s1, result))

macroStep :: MacroMachine -> Config -> Maybe (Int, MacroRule, Config)
macroStep m conf@(s, _) = foldr (<|>) Nothing [ macroRule r conf | r <- rules m s ]

macroRun :: Int -> MacroMachine -> (Result, MacroMachine)
macroRun = macroRun' False

verboseRun :: Int -> MacroMachine -> (Result, MacroMachine)
verboseRun = macroRun' True

data Result = Terminated Int Int
            | OutOfFuel Int
  deriving (Eq, Ord, Show)
  deriving Pretty via (ViaShow Result)

macroRun' :: Bool -> Int -> MacroMachine -> (Result, MacroMachine)
macroRun' verbose fuel m0 = goV m0 Nothing fuel 0 0 initialConfig
  where
    goV m lastRule fuel n k conf@(s, tape) = dbg $ go m lastRule fuel n k conf
      where
        dbg | verbose   = trace $ printf "%7d %3d | %s: %s" n k (show s) (show $ pPrint tape)
            | otherwise = id

    go m _ fuel _ k _ | fuel <= 0 = (OutOfFuel k, m)
    go m _ _ n k (H, _) = (Terminated n k, m)
    go m lastRule fuel !n !k conf@(s, _) =
      case macroStep m conf of
        Nothing        -> error $ show $ text "step failed on" <+> pPrint conf
        Just (w, r, conf) -> goV m' (Just r') (fuel - w) (n + w) (k + 1) conf
          where
            (m', r')
              | Just (s0, r0) <- lastRule
              , Just r' <- batchRule s0 <$> combineRules r0 r =
                -- (if verbose then trace (show $ vcat [ nest 2 $ pPrint r0
                --                                     , "+" <+> pPrint r
                --                                     , "=" <+> pPrint r'
                --                                     ]) else id)
                (addRule s0 r' m, (s0, r'))
              | otherwise = (m, (s, r))


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
  b@(Rule (BatchR (Tape lp x rp) rp₂ _ _) _ w) ->
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
  b@(Rule (BatchL lp₂ (Tape lp x rp) _ _) _ w) ->
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

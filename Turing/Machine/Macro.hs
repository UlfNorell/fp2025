
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
data MacroRule = LHS :=> (State, RHS, Dir, Int)
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
    subsumes (lhs :=> _) (lhs' :=> _) = lhs == lhs'

ruleCost :: MacroRule -> Int
ruleCost (_ :=> (_, _, _, w)) = w

instance Semigroup MacroMachine where
  MacroMachine m <> MacroMachine m' = MacroMachine $ Map.unionWith (++) m m'

instance Monoid MacroMachine where
  mempty = MacroMachine mempty

------------------------------------------------------------------------
-- Building macro rules
------------------------------------------------------------------------

basicRule :: Rule -> MacroMachine
basicRule ((s, i) :-> (s', o, d)) = MacroMachine $
  Map.singleton s [Tape mempty i mempty :=> (s', Tape mempty o mempty, d, 1)]

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
combineRules (lhs₁ :=> (_, rhs₁, d₁, w₁))
             (lhs₂ :=> (s₂', rhs₂, d₂, w₂))
  | Just ((lp₁, rp₁), (ls₂, rs₂)) <- chainMatch lhs₂ rhs₁ d₁ = do
    let lhs@(Tape lp _ rp) = plugLHS lp₁ lhs₁ rp₁
        rhs = plugRHS ls₂ rhs₂ rs₂
    guard $ CList.length lp + CList.length rp < 10
    pure $ lhs :=> (s₂', rhs, d₂, w₁ + w₂)
combineRules _ _ = Nothing

-- Batching ---------------------------------------------------------------

batchRight :: LHS -> RHS -> Maybe (CList Symbol, CList Symbol)
batchRight (Tape lp x rp) (Tape ls y rs)
  | Just rp₂ <- CList.dropPrefix rs (x :@ rp)
  , Just ls₂ <- CList.dropPrefix lp (y :@ ls) = Just (ls₂, rp₂)
batchRight _ _ = Nothing

------------------------------------------------------------------------
-- Running
------------------------------------------------------------------------

matchLHS :: LHS -> Tape -> Maybe (CList Symbol, CList Symbol)
matchLHS (Tape lp x rp) (Tape ls y rs)
  | x == y
  , Just ls' <- CList.dropPrefix lp ls
  , Just rs' <- CList.dropPrefix rp rs = pure (ls', rs')
matchLHS _ _ = Nothing

macroRule :: MacroRule -> Config -> Maybe (MacroRule, Config)
macroRule r@(lhs :=> (s1, rhs, d, w)) (_, tape)
  | Just (ls, rs) <- matchLHS lhs tape = Just (r, (s1, move d $ plugRHS ls rhs rs))
macroRule _ _ = Nothing

macroStep :: MacroMachine -> Config -> Maybe (MacroRule, Config)
macroStep m conf@(s, _) = foldr (<|>) Nothing [ macroRule r conf | r <- rules m s ]

macroRun :: Int -> MacroMachine -> Maybe (Int, Int, Tape, MacroMachine)
macroRun = macroRun' False

verboseRun :: Int -> MacroMachine -> Maybe (Int, Int, Tape, MacroMachine)
verboseRun = macroRun' True

macroRun' :: Bool -> Int -> MacroMachine -> Maybe (Int, Int, Tape, MacroMachine)
macroRun' verbose fuel m0 = goV m0 Nothing fuel 0 0 initialConfig
  where
    goV m lastRule fuel n k conf@(s, tape) = dbg $ go m lastRule fuel n k conf
      where
        dbg | verbose   = trace $ printf "%7d %3d | %s: %s" n k (show s) (show $ pPrint tape)
            | otherwise = id

    go _ _ 0 _ _ _ = Nothing
    go m _ _ n k (H, tape) = pure (n, k, tape, m)
    go m lastRule fuel !n !k conf@(s, _) =
      case macroStep m conf of
        Nothing        -> error $ show $ text "step failed on" <+> pPrint conf
        Just (r, conf) -> goV m' (Just r') (fuel - 1) (n + ruleCost r) (k + 1) conf
          where
            (m', r')
              | Just (s0, r0) <- lastRule
              , Just r' <- combineRules r0 r =
                -- (if verbose then trace (show $ vcat [ nest 2 $ pPrint r0
                --                                     , "+" <+> pPrint r
                --                                     , "=" <+> pPrint r'
                --                                     ]) else id)
                (addRule s0 r' m, (s0, r'))
              | otherwise = (m, (s, r))


------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------

instance Pretty MacroRule where
  pPrint (i :=> o) = sep [ pPrint i <+> text "=>", nest 2 $ pPrint o ]

instance Pretty MacroMachine where
  pPrint (MacroMachine m) = vcat [ (pPrint s <> ":") <+> vcat (map pPrint rs) | (s, rs) <- Map.toList m ]

------------------------------------------------------------------------
-- QuickCheck properties
------------------------------------------------------------------------

instance Arbitrary MacroRule where
  arbitrary = (:=>) <$> genLHS <*> genRHS
    where
      genLHS = genPat
      genRHS = (,,,) <$> arbitrary <*> genPat <*> arbitrary <*> choose (1, 10)
      genPat = Tape <$> short <*> arbitrary <*> short
      short = CList.fromList <$> do
        n <- choose (0, 3)
        vectorOf n arbitrary
  shrink (lhs :=> rhs) =
    [ lhs :=> rhs | lhs <- shrink lhs ] ++
    [ lhs :=> rhs | rhs <- shrink rhs ]

prop_combine :: MacroRule -> MacroRule -> Property
prop_combine r1 r2 =
  case combineRules r1 r2 of
    Nothing -> discard
    Just r3@(lhs :=> _) ->
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
    apply r conf = snd <$> macroRule r conf


module Turing.Machine.Macro where

import Control.Applicative
import Control.Monad
import Data.List.Compressed qualified as CList
import Data.List.Compressed (CList, pattern NilC, pattern (:@))
import Text.Pretty
import Text.Printf
import Test.QuickCheck.Extra
import Debug.Trace

import Turing.Types
import Turing.Tape
import Turing.Machine

-- Starting without batching ----------------------------------------------

type LHS = Tape
type RHS = Tape
data MacroRule = (State, LHS) :=> (State, RHS, Dir, Int)
  deriving (Eq, Ord, Show)
type MacroMachine = [MacroRule]

ruleCost :: MacroRule -> Int
ruleCost (_ :=> (_, _, _, w)) = w

-- Building macro rules ---------------------------------------------------

primMacroRule :: Rule -> MacroRule
primMacroRule ((s, i) :-> (s', o, d)) = (s, Tape mempty i mempty) :=> (s', Tape mempty o mempty, d, 1)

matchLHS :: LHS -> Tape -> Maybe (CList Symbol, CList Symbol)
matchLHS (Tape lp x rp) (Tape ls y rs)
  | x == y
  , Just ls' <- CList.dropPrefix lp ls
  , Just rs' <- CList.dropPrefix rp rs = pure (ls', rs')
matchLHS _ _ = Nothing

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

dropEitherPrefix :: Eq a => CList a -> CList a -> Maybe (CList a, CList a)
dropEitherPrefix xs ys
  | Just ys' <- CList.dropPrefix xs ys = Just (NilC, ys')
  | Just xs' <- CList.dropPrefix ys xs = Just (xs', NilC)
  | otherwise                    = Nothing

-- Find lp and rp such that matchLHS lhs (move d lp[rhs]rp) == Just (ls, rs)
chainMatch :: LHS -> RHS -> Dir -> Maybe ((CList Symbol, CList Symbol), (CList Symbol, CList Symbol))

chainMatch (Tape lp x rp) (Tape ls y rs) L = do
  ((rp₁, lp₁), (rs₁, ls₁)) <- chainMatch (Tape rp x lp) (Tape rs y ls) R
  pure ((lp₁, rp₁), (ls₁, rs₁))

chainMatch (Tape lp x rp) (Tape ls y NilC) R
  | Just (lp₁, ls₁) <- dropEitherPrefix lp (y :@ ls) = Just ((lp₁, rp₁), (ls₁, rs₁))
  where
    rp₁ = x :@ rp
    rs₁ = NilC

chainMatch (Tape lp x rp) (Tape ls y (r :@ rs)) R
  | x == r
  , Just (lp₁, ls₁) <- dropEitherPrefix lp (y :@ ls)
  , Just (rp₁, rs₁) <- dropEitherPrefix rp rs = Just ((lp₁, rp₁), (ls₁, rs₁))
chainMatch _ _ _ = Nothing

combineRules :: MacroRule -> MacroRule -> Maybe MacroRule
combineRules ((s₁, lhs₁) :=> (s₁', rhs₁, d₁, w₁))
             ((s₂, lhs₂) :=> (s₂', rhs₂, d₂, w₂))
  | s₁' == s₂
  , Just ((lp₁, rp₁), (ls₂, rs₂)) <- chainMatch lhs₂ rhs₁ d₁ = do
    let lhs@(Tape lp _ rp) = plugLHS lp₁ lhs₁ rp₁
        rhs = plugRHS ls₂ rhs₂ rs₂
    guard $ CList.length lp + CList.length rp < 10
    pure $ (s₁, lhs) :=> (s₂', rhs, d₂, w₁ + w₂)
combineRules _ _ = Nothing

-- Running a macro machine ------------------------------------------------

macroRule :: MacroRule -> Config -> Maybe (MacroRule, Config)
macroRule r@((s0, lhs) :=> (s1, rhs, d, w)) (s, tape)
  | s == s0, Just (ls, rs) <- matchLHS lhs tape = Just (r, (s1, move d $ plugRHS ls rhs rs))
macroRule _ _ = Nothing

macroStep :: MacroMachine -> Config -> Maybe (MacroRule, Config)
macroStep m conf = foldr (<|>) Nothing [ macroRule r conf | r <- m ]

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
    go m lastRule fuel !n !k conf =
      case macroStep m conf of
        Nothing        -> error $ show $ text "step failed on" <+> pPrint conf
        Just (r, conf) -> goV m' (Just r') (fuel - 1) (n + ruleCost r) (k + 1) conf
          where
            (m', r')
              | Just r0 <- lastRule
              , Just r' <- combineRules r0 r = (r' : m, r')
              | otherwise                    = (m, r)

-- Pretty printing --------------------------------------------------------

instance Pretty MacroRule where
  pPrint (i :=> o) = sep [ pPrint i <+> text "=>", nest 2 $ pPrint o ]

-- QuickCheck properties --------------------------------------------------

instance Arbitrary MacroRule where
  arbitrary = (:=>) <$> genLHS <*> genRHS
    where
      genLHS = (,) <$> arbitrary <*> genPat
      genRHS = (,,,) <$> arbitrary <*> genPat <*> arbitrary <*> choose (1, 10)
      genPat = Tape <$> short <*> arbitrary <*> short
      short = CList.fromList <$> do
        n <- choose (0, 3)
        vectorOf n arbitrary
  shrink (lhs :=> rhs) =
    [ lhs :=> rhs | lhs <- shrink lhs ] ++
    [ lhs :=> rhs | rhs <- shrink rhs ]

prop_combine :: MacroRule -> MacroRule -> Property
prop_combine ((_, lhs₁) :=> (_, rhs₁, d₁, w₁))
             ((_, lhs₂) :=> (_, rhs₂, d₂, w₂)) =
  case combineRules r1 r2 of
    Nothing -> discard
    Just r3@((s, lhs) :=> _) ->
      apply r3 (s, lhs) === (apply r2 =<< apply r1 (s, lhs))
  where
    r1 = (A, lhs₁) :=> (A, rhs₁, d₁, w₁)
    r2 = (A, lhs₂) :=> (A, rhs₂, d₂, w₂)
    apply r conf = snd <$> macroRule r conf

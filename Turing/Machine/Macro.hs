
module Turing.Machine.Macro where

import Control.Applicative
import Data.List.Compressed qualified as CList
import Data.List.Compressed (CList)
import Text.PrettyPrint.HughesPJClass hiding ((<>))

import Turing.Types
import Turing.Tape
import Turing.Machine

-- Starting without batching ----------------------------------------------

type LHS = Tape
type RHS = Tape
data MacroRule = (State, LHS) :=> (State, RHS, Dir, Int)
type MacroMachine = [MacroRule]

-- Building macro rules ---------------------------------------------------

primMacroRule :: Rule -> MacroRule
primMacroRule ((s, i) :-> (s', o, d)) = (s, Tape mempty i mempty) :=> (s', Tape mempty o mempty, d, 1)

-- Running a macro machine ------------------------------------------------

matchLHS :: LHS -> Tape -> Maybe (CList Symbol, CList Symbol)
matchLHS (Tape lp x rp) (Tape ls y rs)
  | x == y
  , Just ls' <- CList.dropPrefix lp ls
  , Just rs' <- CList.dropPrefix rp rs = pure (ls', rs')
matchLHS _ _ = Nothing

plugRHS :: CList Symbol -> RHS -> CList Symbol -> Tape
plugRHS ls0 (Tape ls x rs) rs0 = Tape (ls0 <> ls) x (rs <> rs0)

macroRule :: MacroRule -> Config -> Maybe (Int, Config)
macroRule ((s0, lhs) :=> (s1, rhs, d, w)) (s, tape)
  | s == s0, Just (ls, rs) <- matchLHS lhs tape = Just (w, (s1, move d $ plugRHS ls rhs rs))
macroRule _ _ = Nothing

macroStep :: MacroMachine -> Config -> Maybe (Int, Config)
macroStep m conf = foldr (<|>) Nothing [ macroRule r conf | r <- m ]

macroRun :: Int -> MacroMachine -> Maybe (Int, Int, Tape)
macroRun fuel m = go fuel 0 0 initialConfig
  where
    go 0 _ _ _ = Nothing
    go _ n k (H, tape) = pure (n, k, tape)
    go fuel !n !k conf =
      case macroStep m conf of
        Nothing        -> error $ show $ text "step failed on" <+> pPrint conf
        Just (w, conf) -> go (fuel - 1) (n + w) (k + 1) conf

-- Pretty printing --------------------------------------------------------

instance Pretty MacroRule where
  pPrint (i :=> o) = sep [ pPrint i <+> text "=>", nest 2 $ pPrint o ]

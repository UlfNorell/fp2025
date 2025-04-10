
module Macro where

import Control.Monad
import Data.Map qualified as Map
import Data.Map (Map)
import Data.Monoid
import Data.Bits
import Text.Printf
import Text.PrettyPrint.HughesPJClass hiding ((<>))
import RList
import Tape
import Debug.Trace

{-

Goals
  - JIT compiler for the macro machines in Turing
  - Combine with exploration

Plan

  - Switch macro machine to use CMachine and applyClause
    - How to handle the wall? It's part of the input but shouldn't be part of the output.
      - Maybe make it part of the pattern!
    - Compile single macro steps to compound rules

  - JIT: keep history of how many times two rules are used together and combine them if over a
    threshold (could be low threshold!)
    - analyse rules for batchability
    - could you combine batched rules? might need extension to clause language, but maybe

-}

data Batching = NoBatch
              | BatchL   -- Bind any number of the left-most symbol
              | BatchR   -- Bind any number of the right-most symbol
  deriving (Eq, Ord, Show)

data WallPat = AnyWall | NoWall | YesWall
  deriving (Eq, Ord, Show)

data Pattern = Pattern Batching WallPat [Symbol] [Symbol]
  deriving (Eq, Ord, Show)

data RHSSymbol = Single Symbol | Batched Symbol   -- The same number as was matched in a batched pattern
  deriving (Eq, Ord, Show)

data RHS = RHS [RHSSymbol] [RHSSymbol] Dir
  deriving (Eq, Ord, Show)

data Clause = Pattern :=> RHS
  deriving (Eq, Ord, Show)

data CRule s = CRule Clause s Int  -- Next state and cost
  deriving (Eq, Ord, Show)

newtype CMachine s = CMachine (Map s [CRule s])

-- Applying rules ---------------------------------------------------------

-- The integer is the multiplicity of the batched match (1 if NoBatch)
matchPattern :: Pattern -> Tape -> Maybe (Tape, Int)
matchPattern (Pattern b wall lp rp) (Tape w l r) = do
  let batchLast = not $ (b, wall) == (BatchL, NoWall)
  (l', bl) <- match L batchLast (b == BatchL) lp l
  (r', br) <- match R True      (b == BatchR) rp r
  guard $ matchWall wall l'
  pure (Tape (w - length lp - bl + 1) l' r', max bl br)
  where
    match _ _ _ [] ys = pure (ys, 1)
    match _ bLast True [x] (RList (RLE y n : ys))
      | not bLast, null ys = (y :@ RList ys, n - 1) <$ guard (x == y && n > 1)
      | otherwise          = (RList ys, n) <$ guard (x == y)
    match d bLast b (x : xs) (y :@ ys) = guard (x == y) *> match d bLast b xs ys
    match R bLast b (0 : xs) NilR = match R bLast b xs NilR
    match _ _ _ _ _ = Nothing

    matchWall AnyWall _  = True
    matchWall NoWall  ls = ls /= NilR
    matchWall YesWall ls = ls == NilR

rhsToRLEs :: Int -> [RHSSymbol] -> [RLE Symbol]
rhsToRLEs n rhs = map eval rhs
  where
    eval (Single x)  = RLE x 1
    eval (Batched x) = RLE x n

writeRHS :: Int -> RHS -> Tape -> Tape
writeRHS n (RHS lrhs rrhs d) = writeAndMove d (rhsToRLEs n lrhs) (rhsToRLEs n rrhs)
  where
    writeAndMove L []        rs' = move L . write [] rs'
    writeAndMove L (l : ls') rs' = write ls' (l : rs')
    writeAndMove R ls'       []  = move R . write ls' []
    writeAndMove R ls' (r : rs') = write (r : ls') rs'

    write :: [RLE Symbol] -> [RLE Symbol] -> Tape -> Tape
    write ls' rs' (Tape w ls rs) = Tape (w + lengthR lsR) (lsR <> ls) (rsR <> rs)
      where lsR = foldMap (RList . (:[])) ls'
            rsR = foldMap (RList . (:[])) rs'

applyClause :: Clause -> Tape -> First (Tape, Int)
applyClause (pat :=> rhs) tape = do
  (tape', n) <- First $ matchPattern pat tape
  pure (writeRHS n rhs tape', n)

applyCRule :: CRule s -> Tape -> First (s, Tape, Int)
applyCRule (CRule cl s n) tape = do
  (tape, m) <- applyClause cl tape
  pure (s, tape, n * m)

-- Smarts -----------------------------------------------------------------

batchRule :: (Show s, Eq s) => s -> CRule s -> CRule s
batchRule s r = trace (printf "batchRule %s (%s)" (show s) (show r)) $ batchRule' s r

batchRule' :: Eq s => s -> CRule s -> CRule s
batchRule' s rule@(CRule _ s' _) | s /= s' = rule
batchRule' _ (CRule (Pattern NoBatch w lsP rsP :=> RHS ls (Single r : rs) R) s' n)
  | w /= YesWall
  , rP : _ <- reverse rsP
  , map Single rsP == rs ++ [Single rP] = CRule (Pattern BatchR w lsP rsP :=> RHS ls (Batched r : rs) R) s' n
batchRule' _ rule = rule

-- Pretty printing --------------------------------------------------------

instance Pretty Clause where
  pPrint (pat :=> rhs) = sep [ pPrint pat <+> text "=>", nest 2 $ pPrint rhs ]

instance Pretty Pattern where
  pPrint (Pattern b w ls rs) = ppW w <> sep [ ppL ls, text "∙" <> ppR rs ]
    where
      ppW AnyWall = text "? "
      ppW YesWall = text "| "
      ppW NoWall  = text "… "

      batchIf True  = zipWith ($) (Batched : repeat Single)
      batchIf False = map Single

      ppL (reverse -> ls) = sep $ map pPrint $ batchIf (b == BatchL) ls
      ppR rs = sep $ map pPrint $ batchIf (b == BatchR) rs

instance Pretty RHS where
  pPrint (RHS ls rs d) =
    case d of
      L | l : ls <- ls -> sep [ text " ", ppr ls, text "∙" <> ppr (l : rs) ]
        | otherwise    -> sep [ text "∙_ ", ppr rs ]
      R | r : rs <- rs -> sep [ text " " <> ppr (ls ++ [r]), text "∙" <> if null rs then text "_" else ppr rs ]
        | otherwise    -> sep [ text " " <> ppr ls, text "_ ∙_" ]  -- Impossible
    where
      ppr = sep . punctuate (text " ") . map pPrint

instance Pretty RHSSymbol where
  pPrint (Single  x) = text (show x)
  pPrint (Batched x) = text (show x ++ "ⁿ")

instance Show s => Pretty (CRule s) where
  pPrint (CRule pat s n) = hsep [ pPrint pat, text (show s), parens $ text (show n) <> text " steps"]

instance Show s => Pretty (CMachine s) where
  pPrint (CMachine m) = vcat [ text (show s ++ ":") <+> vcat (map pPrint rs) | (s, rs) <- Map.toList m ]

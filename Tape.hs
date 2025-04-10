
module Tape where

import Control.Monad
import Data.Map (Map)
import Data.Bits
import RList

newtype Symbol = Symbol Int
  deriving (Eq, Ord, Enum)
  deriving newtype (Show, Num, Bits)

data Dir = L | R
  deriving (Eq, Ord, Show, Enum)

data Tape = Tape {-# UNPACK #-} !Int (RList Symbol) (RList Symbol)
  deriving (Eq, Ord, Show)

tape0 :: Tape
tape0 = Tape 0 mempty mempty

look :: Tape -> Symbol
look (Tape _ _ NilR)     = 0
look (Tape _ _ (x :@ _)) = x

write :: Symbol -> Tape -> Tape
write 0 (Tape n ls    NilR)     = Tape n ls       NilR
write x (Tape n ls    NilR)     = Tape n ls (x :@ NilR)
write 0 (Tape n ls (_ :@ NilR)) = Tape n ls       NilR
write x (Tape n ls (_ :@ rs))   = Tape n ls (x :@   rs)

move :: Dir -> Tape -> Tape
move L (Tape n  NilR          rs)  = Tape 0           NilR           rs -- bouncing
move L (Tape n (0 :@ ls)    NilR)  = Tape (n - 1)       ls         NilR
move L (Tape n (x :@ ls)      rs)  = Tape (n - 1)       ls     (x :@ rs)
move R (Tape n  ls      (x :@ rs)) = Tape (n + 1) (x :@ ls)    rs
move R (Tape n  ls          NilR)  = Tape (n + 1) (0 :@ ls)  NilR

-- Tape fragment
data Fragment = [Symbol] :> [Symbol]

data Batching = NoBatch
              | BatchL   -- Bind any number of the left-most symbol
              | BatchR   -- Bind any number of the right-most symbol
  deriving (Eq, Ord, Show)

data Pattern = Pattern Batching [Symbol] [Symbol]
  deriving (Eq, Ord, Show)

data RHSSymbol = Single Symbol | Batched Symbol   -- The same number as was matched in a batched pattern
  deriving (Eq, Ord, Show)

type RHS = ([RHSSymbol], [RHSSymbol])

data CompoundRule s = Fragment :=> (s, Fragment, Int)
type CompoundMachine s = Map s (CompoundRule s)

-- How to represent when the leftmost/rightmost symbol is repeated?
-- Possibly build batching into the rules? Allow matching on xⁿ as the leftmost/rightmost symbol.
-- That seems like a nicer way to do things. Then all the batch logic is moved to the rule compiler.
-- How to represent outputs involving n? For instance 0B 3 7ⁿ -> 0ⁿ⁺¹ C3. Could restrict to only
-- allowing xⁿ, so this one would be 0B 3 7ⁿ -> 0 0ⁿ C3.

-- The integer is the multiplicity of the batched match (1 if NoBatch)
matchPattern :: Pattern -> Tape -> Maybe (Int, Tape)
matchPattern (Pattern b lp rp) (Tape w l r) = do
  (l', bl) <- match (b == BatchL) lp l
  (r', br) <- match (b == BatchR) rp r
  pure (max bl br, Tape (w - length lp - bl + 1) l' r')
  where
    match _ [] ys = pure (ys, 1)
    match True [x] (RList (RLE y n : ys)) = (RList ys, n) <$ guard (x == y)
    match b (x : xs) (y :@ ys) = guard (x == y) *> match b xs ys

matchFragment :: Fragment -> Tape -> Maybe Tape
matchFragment (lp :> rp) (Tape w l r) = do
  l' <- match lp l
  r' <- match rp r
  pure $ Tape (w - length lp) l' r'
  where
    match [] ys = pure ys
    match (x : xs) (y :@ ys) = guard (x == y) *> match xs ys

{-# INLINE applyRule #-}
applyRule :: (Show s, Eq s) => s -> (s, Symbol, Dir) -> Tape -> (Tape, Int)

-- Hack the bb4 rule
applyRule s (s', o, d) (Tape w ls (RList (RLE 0 1 : RLE 3 1 : RLE 7 n : rs)))
  | show s == "(B,L)", show s' == "(C,R)" = (tape', 9 * n + 1)
  where
    tape' = Tape (w + n + 1) (RList [RLE 0 (n + 1)] <> ls) (3 :@ RList rs)

applyRule s (s', o, d) tape
  | s /= s' = (move d $ write o tape, 1)
applyRule s (s', o, R) tape@(Tape w ls rs) =
  case rs of
    RList []             -> (Tape (w + 1) (o :@ ls) rs, 1)
    RList (RLE i n : rs) -> (Tape (w + n) (RList [RLE o n] <> ls) (RList rs), n)
-- applyRule _ (_, o, R) tape = (move R $ write o tape, 1)
applyRule s (s', o, L) tape@(Tape w (RList [RLE i n]) (j :@ rs))
  | i == j = (tape', n)
  where tape' = Tape (w - n) mempty $ i :@ add o rs
        add 0 NilR = NilR
        add o rs   = RList [RLE o n] <> rs
applyRule s (s', o, L) tape@(Tape w (RList (RLE i n : ls)) (j :@ rs))
  | i == j = (tape', n + 1)
  where tape' = move L $ Tape (w - n) (RList ls) $ add o rs
        add 0 NilR = NilR
        add o rs   = RList [RLE o (n + 1)] <> rs
applyRule _ (_, o, L) tape = (move L $ write o tape, 1)
-- applyRule _ (_, o, d) tape = (move d $ write o tape, 1)


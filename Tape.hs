
module Tape where

import Control.Monad
import Data.Map (Map)
import Data.Bits
import Test.QuickCheck
import RList

newtype Symbol = Symbol Int
  deriving (Eq, Ord, Enum)
  deriving newtype (Show, Num, Bits)

data Dir = L | R
  deriving (Eq, Ord, Show, Enum)

data Tape = Tape {-# UNPACK #-} !Int (RList Symbol) (RList Symbol)
  deriving (Eq, Ord, Show)

mkTape :: [Symbol] -> [Symbol] -> Tape
mkTape ls rs = Tape (length ls) (toRList ls) (toRList rs)

tape0 :: Tape
tape0 = mkTape [] []

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

{-# INLINE applyRule #-}
applyRule :: (Show s, Eq s) => s -> (s, Symbol, Dir) -> Tape -> (Tape, Int)
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

-- QuickCheck tests -------------------------------------------------------

instance Arbitrary Dir where
  arbitrary = elements [L, R]
  shrink L = []
  shrink R = [L]

instance Arbitrary Symbol where
  arbitrary = Symbol <$> choose (0, 1)
  shrink (Symbol x) = map Symbol (shrink x)



module Turing.Types where

import Text.Pretty
import Test.QuickCheck

newtype Symbol = Symbol Int
  deriving (Eq, Ord, Enum)
  deriving newtype (Show, Num, Pretty)

data Dir = L | R
  deriving (Eq, Ord, Show, Enum)

op :: Dir -> Dir
op L = R
op R = L

data State = A | B | C | D | E | F | H
  deriving (Eq, Ord, Show, Enum, Bounded)

instance Pretty Dir   where pPrint = text . show
instance Pretty State where pPrint = text . show

instance Arbitrary Symbol where
  arbitrary = elements [0, 1]
  shrink (Symbol n) = map Symbol $ shrink n

instance Arbitrary Dir where
  arbitrary = elements [L, R]
  shrink L = [R]
  shrink R = []

instance Arbitrary State where
  arbitrary = elements [A .. H]
  shrink s = filter (< s) [A .. s]

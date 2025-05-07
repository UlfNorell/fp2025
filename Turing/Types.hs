
module Turing.Types where

import Text.PrettyPrint.HughesPJClass hiding ((<>))

newtype Symbol = Symbol Int
  deriving (Eq, Ord, Enum)
  deriving newtype (Show, Num, Pretty)

data Dir = L | R
  deriving (Eq, Ord, Show, Enum)

data State = A | B | C | D | E | F | H
  deriving (Eq, Ord, Show)

instance Pretty Dir   where pPrint = text . show
instance Pretty State where pPrint = text . show


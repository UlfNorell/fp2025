module Turing.Tape where

import Text.PrettyPrint.HughesPJClass hiding ((<>))

import Data.List.Compressed qualified as CList
import Data.List.Compressed (CList, pattern NilC, pattern (:@))
import Turing.Types

-- Type -------------------------------------------------------------------

data Tape = Tape (CList Symbol) Symbol (CList Symbol)
  deriving (Show, Eq, Ord)

-- Basic operations -------------------------------------------------------

initialTape :: Tape
initialTape = Tape mempty 0 mempty

look :: Tape -> Symbol
look (Tape _ x _) = x

write :: Symbol -> Tape -> Tape
write x (Tape ls _ rs) = Tape ls x rs

move :: Dir -> Tape -> Tape
move L (Tape NilC x rs)      = Tape NilC x rs
move L (Tape (l :@ ls) x rs) = Tape ls l (x :@ rs)
move R (Tape ls x NilC)      = Tape (x :@ ls) 0 NilC
move R (Tape ls x (r :@ rs)) = Tape (x :@ ls) r rs

-- Pretty printing --------------------------------------------------------

instance Pretty Tape where
  pPrint (Tape ls x rs) = hsep [pPrint (CList.reverse ls), brackets $ pPrint x, pPrint rs]

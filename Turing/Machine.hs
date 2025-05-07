
module Turing.Machine where

import Control.Applicative
import Text.PrettyPrint.HughesPJClass

import Turing.Types
import Turing.Tape

-- Primitive machines -----------------------------------------------------

data Rule = (State, Symbol) :-> (State, Symbol, Dir)
  deriving (Eq, Ord, Show)

type Machine = [Rule]

-- Running ----------------------------------------------------------------

type Config = (State, Tape)

initialConfig :: Config
initialConfig = (A, initialTape)

primRule :: Rule -> Config -> Maybe Config
primRule ((s0, i) :-> (s1, o, d)) (s, tape)
  | s == s0, i == look tape = Just (s1, move d (write o tape))
  | otherwise               = Nothing

primStep :: Machine -> Config -> Maybe Config
primStep rs conf = foldr (<|>) Nothing [ primRule r conf | r <- rs ]

primRun :: Int -> Machine -> Maybe (Int, Tape)
primRun fuel m = go fuel 0 initialConfig
  where
    go 0 _ _ = Nothing
    go _ n (H, tape) = pure (n, tape)
    go fuel !n conf =
      case primStep m conf of
        Nothing   -> error $ show $ text "step failed on" <+> pPrint conf
        Just conf -> go (fuel - 1) (n + 1) conf

-- Pretty printing --------------------------------------------------------

instance Pretty Rule where
  pPrint = text . show


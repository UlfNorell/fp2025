
module Turing.Machine where

import Control.Applicative
import Text.Pretty
import Text.Printf
import Debug.Trace

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

primRun :: Bool -> Int -> Machine -> Maybe (Int, Tape)
primRun verbose fuel m = case primRun' verbose fuel m initialConfig of
  (n, (H, tape)) -> Just (n, tape)
  _              -> Nothing

primRun' :: Bool -> Int -> Machine -> Config -> (Int, Config)
primRun' verbose fuel m = go fuel 0
  where
    go 0 n conf = (n, conf)
    go _ n conf@(H, _) = (n, conf)
    go fuel !n conf =
      case primStep m conf of
        Nothing   -> error $ show $ text "step failed on" <+> pPrint conf
        Just conf@(s, tape) -> dbg $ go (fuel - 1) (n + 1) conf
          where
            dbg | verbose   = trace $ printf "%7d | %s: %s" (n + 1) (show s) (show $ pPrint tape)
                | otherwise = id

-- Pretty printing --------------------------------------------------------

instance Pretty Rule where
  pPrint = text . show


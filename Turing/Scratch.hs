
module Turing.Scratch
  ( module X
  , module Turing.Scratch
  ) where

import Turing.Types as X
import Turing.Tape as X
import Turing.Machine as X
import Turing.Machine.Macro as X
import Turing.Examples as X
import Text.Pretty as X
import Test.QuickCheck.Extra as X
import Data.List.Compressed as X (CList(..), Rep(..), pattern NilC, pattern (:@))

import Data.List.Compressed qualified as CList
import Data.Map qualified as Map

{-

Goals
  - No fixed macro digits (discover dynamically by combining rules)
  - Exploration and jitting working together

Notes
  √ Symmetrical tape
    - Focused digit separately, or part of both left and right? Surely separate?
  - What is a nice pattern abstraction for compressed lists?
  - Add infinity to the repeats?

Steps
  √ Compressed list tape
  √ Basic run function
  √ Rule type rich enough to allow combined rules
    √ combine
    √ quickcheck tests
    √ also batched rules
  √ Run function with jit
  √ Exploration with jit
    √ basic exploration
    √ shortcutting rules
  √ Memory issue!
  - More rule combination
    - Combining batched rules?
    - Wall pattern? Currently we combine rules that are applied after each other at the wall, but
      when combining we ignore the wall. This (I think) just produces a rule that simply doesn't
      apply in the original state.
-}

{-
  A macro rule consists of
    - in/out state
    - pattern and replacement
    - wall pattern (does this have to include NoWall now that we don't have macro digits?)
    - I think I really do want a direction as well?
      - That might allow skipping the wall pattern?
    - how are batching done in patterns?
-}

xs = CList [[0, 0, 1, 0] :^ 1_000_000_000_000]
ys = CList.fromList [0, 0, 1, 0]

mkR :: Wall -> Tape -> Tape -> Dir -> MacroRule
mkR w lhs rhs d = Rule (Clause w lhs rhs d) A 1

mkBR :: Tape -> [Symbol] -> [Symbol] -> Tape -> MacroRule
mkBR lhs rp ls rhs = Rule (BatchR lhs (CList.fromList rp) (CList.fromList ls) rhs) A 1

mkBL :: [Symbol] -> Tape -> Tape -> [Symbol] -> MacroRule
mkBL lp lhs rhs rs = Rule (BatchL (CList.fromList lp) lhs rhs (CList.fromList rs)) A 1

-- … 0 [0] ε => ε [0] 1 L, A (cost 2)
r1 = mkR NoWall (mkTape [0] 0 []) (mkTape [] 0 [1]) L
-- 0ⁿ ε [0] ε => ε [1] ε 1ⁿ, A (cost 1)
r2 = mkBL [0] (mkTape [] 0 []) (mkTape [] 1 []) [1]

-- … 0 [0] ε => ε [0] 1 L, A (cost 2)
r = mkR NoWall (mkTape [] 1 [0]) (mkTape [] 1 [1]) R
b = head $ batchRule A r

app r tape = case macroRule r (A, tape) of
  Just (_, _, _, (_, tape)) -> Just tape
  Nothing -> Nothing

-- Benchmarking -----------------------------------------------------------

-- bb3 10,000

-- First working version
--  Loop            2926  (21.9%)
--  OutOfFuel       3429  (25.7%)
--  StuckLeft       1250  ( 9.4%)
--  Terminated      5748  (43.0%)
--  Total          13353
--  Average steps:  44.8
--  Max steps:      4255
--  Time:            3.8s

-- Strip duplicate batched rules
--  Time:            2.5s

badBB3₁ :: Machine
badBB3₁ = [ (A, 0) :-> (B, 1, L)
          , (A, 1) :-> (A, 0, R)
          , (B, 0) :-> (C, 0, L)
          , (B, 1) :-> (A, 1, L)
          , (C, 0) :-> (A, 0, L) ]

-- Wall bouncing
--  Time:            0.6s
--  Average steps:  31.4
--  Max steps:      4009

badBB3₂ :: Machine
badBB3₂ = [ (A, 0) :-> (B, 1, L)
          , (A, 1) :-> (A, 0, R)
          , (B, 0) :-> (C, 0, L)
          , (B, 1) :-> (B, 0, R)
          , (C, 0) :-> (A, 1, L)
          ]

-- Better wall bouncing
--  Loop            2927  (21.9%)
--  OutOfFuel       3428  (25.7%)
--  StuckLeft       1250  ( 9.4%)
--  Terminated      5748  (43.0%)
--  Total          13353
--  Average steps: 24.7
--  Time:           0.4s
--  Max steps:     1225

-- BB4 10,000
-- Loop          528975  (25.5%)
-- OutOfFuel     611251  (29.5%)
-- StuckLeft     142953  ( 6.9%)
-- Terminated    787694  (38.0%)
-- Total        2070873
-- Average steps: 37.5
-- Max steps:     2229
-- Time:         61m42s

badBB3₃ :: Machine
badBB3₃ = [ (A, 1) :-> (B, 1, L)
          , (A, 0) :-> (A, 1, L)
          , (B, 0) :-> (C, 1, L)
          , (B, 1) :-> (B, 0, R)
          , (C, 0) :-> (A, 0, L) ]

-- Generalized wall bounce
--  Loop            2921  (21.9%)
--  OutOfFuel       3434  (25.7%)
--  StuckLeft       1250  ( 9.4%)
--  Terminated      5748  (43.0%)
--  Total          13353
--  Average steps: 22.7
--  Max steps:     1184
--  Time:          1.5s

-- Merge wall bounce and :=>
--  Loop            2918  (21.9%)
--  OutOfFuel       3437  (25.7%)
--  StuckLeft       1250  ( 9.4%)
--  Terminated      5748  (43.0%)
--  Total          13353
--  Average steps: 22.0
--  Max steps:     1181
--  Time:          2.8s

badBB3₄ :: Machine
badBB3₄ = [ (A, 1) :-> (B, 0, R)
          , (A, 0) :-> (A, 1, L)
          , (B, 1) :-> (B, 0, R)
          , (B, 0) :-> (C, 1, L)
          , (C, 0) :-> (A, 0, L) ]

-- Better combineRules
--  Loop            2941  (22.0%)
--  OutOfFuel       3414  (25.6%)
--  StuckLeft       1250  ( 9.4%)
--  Terminated      5748  (43.0%)
--  Total          13353
--  Average steps: 17.9
--  Max steps:     2012
--  Time:          1.3s

badBB3₅ :: Machine
badBB3₅ = [ (A, 1) :-> (A, 1, R)
          , (A, 0) :-> (B, 0, R)
          , (B, 1) :-> (C, 1, L)
          , (B, 0) :-> (B, 1, L)
          , (C, 1) :-> (A, 1, L) ]

-- AnyWall pattern
--  Loop            2941  (22.0%)
--  OutOfFuel       3414  (25.6%)
--  StuckLeft       1250  ( 9.4%)
--  Terminated      5748  (43.0%)
--  Total          13353
--  Average steps: 15.4
--  Max steps:     2010
--  Time:          1.3s

badBB3₆ :: Machine
badBB3₆ = [ (A, 1) :-> (B, 1, L)
          , (A, 0) :-> (A, 1, L)
          , (B, 1) :-> (C, 1, L)
          , (C, 0) :-> (A, 0, R)
          , (C, 1) :-> (C, 1, R) ]

-- Combining with batched rules
--  Loop            2941  (22.0%)
--  OutOfFuel       3414  (25.6%)
--  StuckLeft       1250  ( 9.4%)
--  Terminated      5748  (43.0%)
--  Total          13353
--  Average steps: 15.0
--  Max steps:     1271
--  Time:          1.3s

-- Quite an interesting counting machine
badBB3₇ :: Machine
badBB3₇ = [ (A, 1) :-> (B, 0, R)
          , (A, 0) :-> (A, 1, L)
          , (B, 1) :-> (B, 0, R)
          , (B, 0) :-> (C, 1, L)
          , (C, 0) :-> (A, 0, L) ]

badBB3₈ :: Machine
badBB3₈ = [ (A, 1) :-> (C, 1, R)
          , (A, 0) :-> (B, 1, L)
          , (B, 1) :-> (C, 1, L)
          , (C, 0) :-> (A, 1, R)
          , (C, 1) :-> (C, 0, L) ]

-- Improved batch rule combination
--  Loop            2941  (22.0%)
--  OutOfFuel       3414  (25.6%)
--  StuckLeft       1250  ( 9.4%)
--  Terminated      5748  (43.0%)
--  Total          13353
--  Average steps: 14.3 - 128.4
--  Max steps:     1088 - 38,511
--  Time:          2.1s - 8.7s

badBB3₉ :: Machine
badBB3₉ = [ (A, 1) :-> (C, 0, R)
          , (A, 0) :-> (B, 1, L)
          , (B, 1) :-> (C, 0, L)
          , (C, 1) :-> (A, 1, R)
          , (C, 0) :-> (A, 1, R) ]

-- Batching with last step in wrong direction
-- Loop            2941  (22.0%)
-- OutOfFuel       3414  (25.6%)
-- StuckLeft       1250  ( 9.4%)
-- Terminated      5748  (43.0%)
-- Total          13353
-- Average steps: 14.2  - 109.1
-- Max steps:     1088  - 38,238
-- Time:          2.1s  - 8.3s

badBB3₁₀ :: Machine
badBB3₁₀ = [ (A, 1) :-> (B, 0, R)
           , (A, 0) :-> (A, 1, L)
           , (B, 1) :-> (B, 0, R)
           , (B, 0) :-> (C, 1, L)
           , (C, 0) :-> (A, 0, L) ]

-- Fix cost bug
--  Loop            2941  (22.0%)
--  OutOfFuel       3414  (25.6%)
--  StuckLeft       1250  ( 9.4%)
--  Terminated      5748  (43.0%)
--  Total          13353
--  Average steps: 13.1   - 102.2
--  Max steps:     735    - 34,301
--  Time:          1.6s   - 5.3s

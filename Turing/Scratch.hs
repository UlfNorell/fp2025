
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

-- ε [0] 0³ (0⁴)ⁿ => (010²)ⁿ 010 [0] ε, A (cost 8)
r :: MacroRule
r = Rule (BatchR (Tape (CList []) 0 (CList [[0] :^ 3]))
                 (CList [[0] :^ 4])
                 (CList [[0] :^ 2,[1,0] :^ 1])
                 (Tape (CList [[0,1,0] :^ 1]) 0 (CList [])))
         A 8

conf = (A,Tape (CList [[0] :^ 2,[1,0] :^ 1]) 0 (CList [[0] :^ 999999999999996]))

xs = CList [[0, 0, 1, 0] :^ 1_000_000_000_000]
ys = CList.fromList [0, 0, 1, 0]

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

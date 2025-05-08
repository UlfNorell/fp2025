
module Turing.Scratch where

import Turing.Types
import Turing.Tape
import Turing.Machine
import Turing.Machine.Macro

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
  - Rule type rich enough to allow combined rules
    - combine
    - quickcheck tests
    - also batched rules
  - Run function with jit
  - Exploration with jit
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

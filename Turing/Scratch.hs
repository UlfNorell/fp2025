
module Turing.Scratch where

import Turing.Types
import Turing.Tape

{-

Goals
  - No fixed macro digits (discover dynamically by combining rules)
  - Exploration and jitting working together

Notes
  - Symmetrical tape
    - Focused digit separately, or part of both left and right? Surely separate?
  - What is a nice pattern abstraction for compressed lists?

Steps
  - Compressed list tape
  - Basic run function
  - Rule type rich enough to allow combined rules
    - also batched rules
  - Run function with jit
  - Exploration with jit
-}


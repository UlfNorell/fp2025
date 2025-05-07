
module Turing.Examples where

import Turing.Types
import Turing.Machine

-- Example machines -------------------------------------------------------

-- Score: 2
bb1 :: Machine
bb1 = [ (A, 0) :-> (A, 1, L)
      , (A, 1) :-> (H, 0, L)
      ]

-- Score: 10
bb2 :: Machine
bb2 = [ (A, 0) :-> (B, 1, L)
      , (A, 1) :-> (H, 0, L)
      , (B, 0) :-> (A, 1, L)
      , (B, 1) :-> (B, 0, R)
      ]

-- Score: 45
bb3 :: Machine
bb3 = [ (A, 0) :-> (B, 0, L)
      , (A, 1) :-> (C, 1, L)
      , (B, 0) :-> (C, 1, R)
      , (B, 1) :-> (H, 0, L)
      , (C, 0) :-> (A, 1, L)
      , (C, 1) :-> (C, 0, R) ]

-- Score: 3,456
bb4 :: Machine
bb4 = [ (A, 0) :-> (A, 1, L)
      , (A, 1) :-> (B, 0, L)
      , (B, 0) :-> (C, 0, R)
      , (B, 1) :-> (C, 1, R)
      , (C, 0) :-> (A, 0, R)
      , (C, 1) :-> (D, 0, R)
      , (D, 0) :-> (H, 0, L)
      , (D, 1) :-> (B, 0, R) ]

-- Score: 449,336
bb5 :: Machine
bb5 = [ (A, 0) :-> (B, 0, R)
      , (B, 0) :-> (C, 0, L)
      , (C, 0) :-> (D, 1, R)
      , (D, 0) :-> (B, 1, L)
      , (B, 1) :-> (A, 1, R)
      , (A, 1) :-> (B, 1, R)
      , (C, 1) :-> (D, 0, R)
      , (D, 1) :-> (E, 1, R)
      , (E, 1) :-> (C, 0, R)
      , (E, 0) :-> (H, 0, L) ]

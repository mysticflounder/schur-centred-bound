/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import ClassicalSchur

/-!
# Proofs of the statements of `Challenge.lean`

This module imports the library `ClassicalSchur`. The library defines the
seven definitions of `Challenge.lean` with the same names and the same bodies,
and proves its fourteen theorems with the same names and statements:

* `ClassicalSchur.Basic`: `SumFree`, `CoveredBySumFree`.
* `ClassicalSchur.Ramsey`: `TriangleRamsey`.
* `ClassicalSchur.SchurBound`: `triangleRamsey_succ`, the centred bound
  `not_coveredBySumFree_Icc_of_triangleRamsey`, and its cases
  `not_coveredBySumFree_Icc_fourteen_three` (`S(3) ≤ 13`) and
  `not_coveredBySumFree_Icc_six_of_triangleRamsey_four_sixtyOne`
  (`R_4(3) ≤ 61` implies `S(6) ≤ 1801`).
* `ClassicalSchur.Frontier`: `SchurColoring`, `colorNbhd`, `centralNbhd`,
  `endpointNbhd`, the two bridges between Schur colourings and sumfree covers,
  and the frontier theorems up to `schur_six_frontier_structure`.

The comparator checks that each definition here is the same constant as in
`Challenge.lean`, and that each theorem has the same statement and uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

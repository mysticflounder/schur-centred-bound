/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import Mathlib

/-!
# Sumfree sets and covers by sumfree sets

* `SumFree S`: no `x, y ∈ S` with `x + y ∈ S`; the case `x = y` is included.
* `CoveredBySumFree X n`: `X` is contained in the union of `n` sumfree sets.
  The sets need not be disjoint or contained in `X`.

The Schur number `S(n)` is the largest `N` such that `[1, N]` is covered by
`n` sumfree sets, so `¬ CoveredBySumFree (Set.Icc 1 (N + 1)) n` says
`S(n) ≤ N`. The definitions follow S. Eliahou and M. P. Revuelta, *The Schur
degree of additive sets*, Discrete Math. 344(5) (2021) 112332,
doi:10.1016/j.disc.2021.112332, cited below as ER.
-/

@[expose] public section

namespace ClassicalSchur

/-- A set of naturals is sumfree when it has no `x, y, z` with `x + y = z`;
`x = y` is allowed (ER §2.3: `(S + S) ∩ S = ∅`). -/
def SumFree (S : Set ℕ) : Prop := ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S

/-- `X` is covered by `n` sumfree sets (ER Definition 2.1). -/
def CoveredBySumFree (X : Set ℕ) (n : ℕ) : Prop :=
  ∃ C : Fin n → Set ℕ, (∀ i, SumFree (C i)) ∧ X ⊆ ⋃ i, C i

end ClassicalSchur

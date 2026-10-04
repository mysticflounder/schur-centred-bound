/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import Mathlib

/-!
# Schur numbers from triangle Ramsey numbers: the centred bound and its frontier

This file states the results of the repository. It imports only Mathlib. The
proofs are in the library `ClassicalSchur`, and `Solution.lean` makes them
available under the same names.

**The centred bound.** If every colouring with `k` colours of the pairs of `r`
points has a monochromatic triangle (`R_k(3) ≤ r`), then `[1, 2((k + 1)q + 1)]`
with `q = ⌊(r − 1)/2⌋` is not covered by `k + 1` sumfree sets, that is,
`S(k + 1) ≤ 2(k + 1)⌊(r − 1)/2⌋ + 1`
(`not_coveredBySumFree_Icc_of_triangleRamsey`). With `R_2(3) ≤ 6` this gives
`S(3) ≤ 13`. With the hypothesis `R_4(3) ≤ 61` it gives `R_5(3) ≤ 302` and
`S(6) ≤ 1801`.

**The frontier.** The other theorems describe a Schur colouring of the largest
interval that the centred bound allows. For six colours under `R_4(3) ≤ 61`
(`schur_six_frontier_structure`), a Schur colouring of `[1, 1801]` gives five
sets of 60 points. Each is closed under `x ↦ 1800 − x` with no fixed point, and
its differences use at most four colours. These theorems do not exclude such a
colouring, so they do not prove `S(6) ≤ 1800`.

**The hypothesis `TriangleRamsey 4 61`.** It is the statement `R_4(3) ≤ 61`.
This repository does not prove it. Every theorem that uses it takes it as an
explicit argument. `R_4(3) ≤ 61` is a computer-assisted claim of M. Tatarevic
(2026, https://github.com/milostatarevic/r3333-upper-bound). The bound
`R_4(3) ≤ 62` is published.
-/

@[expose] public section

namespace ClassicalSchur

/-- A set `S` of natural numbers is *sumfree* if there are no `x, y ∈ S` with
`x + y ∈ S`. The case `x = y` is included, so a sumfree set contains no `x`
together with `2x`, and does not contain `0`. -/
def SumFree (S : Set ℕ) : Prop := ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S

/-- `X` is contained in the union of `n` sumfree sets. The sets need not be
disjoint or contained in `X`. The Schur number `S(n)` is the largest `N` such
that `CoveredBySumFree (Set.Icc 1 N) n` holds, so
`¬ CoveredBySumFree (Set.Icc 1 (M + 1)) n` gives `S(n) ≤ M`. -/
def CoveredBySumFree (X : Set ℕ) (n : ℕ) : Prop :=
  ∃ C : Fin n → Set ℕ, (∀ i, SumFree (C i)) ∧ X ⊆ ⋃ i, C i

/-- `R_k(3) ≤ N`: for every finite set `V` of at least `N` natural numbers and
every map `c` that gives each pair `x < y` of `V` a colour `c x y` from a set
`K` of at most `k` colours (colours are natural numbers), there are
`x < y < z` in `V` with `c x y = c y z = c x z`. -/
def TriangleRamsey (k N : ℕ) : Prop :=
  ∀ (V K : Finset ℕ) (c : ℕ → ℕ → ℕ), K.card ≤ k → N ≤ V.card →
    (∀ x ∈ V, ∀ y ∈ V, x < y → c x y ∈ K) →
    ∃ x ∈ V, ∃ y ∈ V, ∃ z ∈ V, x < y ∧ y < z ∧ c x y = c y z ∧ c x y = c x z

open Finset

/-- `c` is a *Schur colouring* of `[1, N]` with `n` colours: there are no
`x, y ≥ 1` with `x + y ≤ N` and `c x = c y = c (x + y)`. The case `x = y` is
included. The values of `c` outside `[1, N]` are not constrained. -/
def SchurColoring {n : ℕ} (N : ℕ) (c : ℕ → Fin n) : Prop :=
  ∀ x y, 0 < x → 0 < y → x + y ≤ N → c x = c y → c (x + y) ≠ c x

/-- The *colour-`i` neighbourhood* of `v` in the finite set `V` for the
difference colouring of `c`: the points `w ∈ V` with `w ≠ v` and
`c |v − w| = i`. -/
def colorNbhd {n : ℕ} (c : ℕ → Fin n) (V : Finset ℕ) (v : ℕ) (i : Fin n) : Finset ℕ :=
  (V.erase v).filter fun w => c (Nat.dist v w) = i

/-- The *central neighbourhood*: the colour-`q` neighbourhood of the centre `m`
in `{0, 1, …, 2m + 1}` (the point `0` is included), where `q = c (m + 1)` is
the colour of the edge from `m` to the endpoint `2m + 1`. -/
def centralNbhd {n : ℕ} (c : ℕ → Fin n) (m : ℕ) : Finset ℕ :=
  colorNbhd c (range (2 * m + 2)) m (c (m + 1))

/-- The *endpoint neighbourhood* of colour `i`: the colour-`i` neighbourhood of
the endpoint `2m + 1` inside the central neighbourhood. -/
def endpointNbhd {n : ℕ} (c : ℕ → Fin n) (m : ℕ) (i : Fin n) : Finset ℕ :=
  colorNbhd c (centralNbhd c m) (2 * m + 1) i

/-- One step of the pigeonhole recursion: `R_k(3) ≤ N` implies
`R_{k+1}(3) ≤ (k + 1)(N − 1) + 2`. -/
theorem triangleRamsey_succ {k N : ℕ} (hR : TriangleRamsey k N) :
    TriangleRamsey (k + 1) ((k + 1) * (N - 1) + 2) := by
  sorry

/-- **The centred bound.** If `R_k(3) ≤ r`, then `[1, 2((k + 1)⌊(r − 1)/2⌋ + 1)]`
is not covered by `k + 1` sumfree sets, so
`S(k + 1) ≤ 2(k + 1)⌊(r − 1)/2⌋ + 1`. -/
theorem not_coveredBySumFree_Icc_of_triangleRamsey {k r : ℕ} (hR : TriangleRamsey k r) :
    ¬ CoveredBySumFree (Set.Icc 1 (2 * ((k + 1) * ((r - 1) / 2) + 1))) (k + 1) := by
  sorry

/-- `S(3) ≤ 13`: `[1, 14]` is not covered by three sumfree sets. This is the
centred bound with `R_2(3) ≤ 6`; the bound is exact, since `S(3) = 13`. -/
theorem not_coveredBySumFree_Icc_fourteen_three : ¬ CoveredBySumFree (Set.Icc 1 14) 3 := by
  sorry

/-- `R_4(3) ≤ 61` implies `S(6) ≤ 1801`: `[1, 1802]` is not covered by six
sumfree sets. `R_4(3) ≤ 61` is a hypothesis, not proved here. -/
theorem not_coveredBySumFree_Icc_six_of_triangleRamsey_four_sixtyOne
    (h : TriangleRamsey 4 61) : ¬ CoveredBySumFree (Set.Icc 1 1802) 6 := by
  sorry

/-- A Schur colouring of `[1, N]` with `n` colours gives a cover of `[1, N]`
by `n` sumfree sets. -/
theorem coveredBySumFree_of_schurColoring {n N : ℕ} {c : ℕ → Fin n}
    (hc : SchurColoring N c) : CoveredBySumFree (Set.Icc 1 N) n := by
  sorry

/-- A cover of `[1, N]` by `n ≥ 1` sumfree sets gives a Schur colouring of
`[1, N]` with `n` colours. -/
theorem exists_schurColoring_of_coveredBySumFree {n N : ℕ} (hn : 0 < n)
    (h : CoveredBySumFree (Set.Icc 1 N) n) : ∃ c : ℕ → Fin n, SchurColoring N c := by
  sorry

/-- **Balanced colour classes.** Let `R_k(3) ≤ 2t + 2`, `m = (k + 1)t`, and
let `c` be a Schur colouring of `[1, 2m + 1]` with `k + 1` colours. Then each
colour occurs exactly `t` times in `[1, m]`. -/
theorem card_filter_Icc_eq_of_frontier {k t m : ℕ} (hR : TriangleRamsey k (2 * t + 2))
    (hm : m = (k + 1) * t) {c : ℕ → Fin (k + 1)} (hc : SchurColoring (2 * m + 1) c)
    (j : Fin (k + 1)) : ((Icc 1 m).filter fun d => c d = j).card = t := by
  sorry

/-- **The central neighbourhood.** Let `R_k(3) ≤ u + 1`, `2t = (k + 1)u`,
`m = (k + 2)t`, and let `c` be a Schur colouring of `[1, 2m + 1]` with `k + 2`
colours. Then the central neighbourhood has `2t + 1` points. -/
theorem card_centralNbhd_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) : (centralNbhd c m).card = 2 * t + 1 := by
  sorry

/-- **Nested saturation.** Under the hypotheses of
`card_centralNbhd_of_frontier`, each point `v` of the central neighbourhood
`V` has exactly `u` neighbours in `V` of each colour `i ≠ c (m + 1)`. -/
theorem card_colorNbhd_centralNbhd_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) {v : ℕ} (hv : v ∈ centralNbhd c m) {i : Fin (k + 2)}
    (hi : i ≠ c (m + 1)) : (colorNbhd c (centralNbhd c m) v i).card = u := by
  sorry

/-- **Automorphism extension.** Let `col` colour the ordered pairs of `α`, let
`J` map the finite set `W` to itself with `J (J x) = x` and
`col (J x) (J y) = col x y` on `W`, and let `e ∉ W`. If `v ∈ W` and `J v` have
the same number of neighbours of each colour in `W ∪ {e}` (other than
themselves), then `col v e = col (J v) e`. -/
theorem color_eq_of_card_filter_eq {α γ : Type*} [DecidableEq α] [DecidableEq γ]
    (col : α → α → γ) {W : Finset α} {e : α} (he : e ∉ W) (J : α → α)
    (hJ : ∀ x ∈ W, J x ∈ W) (hJJ : ∀ x ∈ W, J (J x) = x)
    (hcol : ∀ x ∈ W, ∀ y ∈ W, col (J x) (J y) = col x y) {v : α} (hv : v ∈ W)
    (hdeg : ∀ i, (((insert e W).erase v).filter fun w => col v w = i).card =
      (((insert e W).erase (J v)).filter fun w => col (J v) w = i).card) :
    col v e = col (J v) e := by
  sorry

/-- **Forced reflection.** Under the hypotheses of
`card_centralNbhd_of_frontier`, if `1 ≤ d ≤ m` and `c d = c (m + 1)`, then
`c (m + 1 − d) = c (m + 1 + d)`. -/
theorem color_reflect_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) {d : ℕ} (hd : 0 < d) (hdm : d ≤ m)
    (hq : c d = c (m + 1)) : c (m + 1 - d) = c (m + 1 + d) := by
  sorry

/-- **Paired endpoint neighbourhoods.** Under the hypotheses of
`card_centralNbhd_of_frontier`, for each colour `i ≠ c (m + 1)` the endpoint
neighbourhood `P` of colour `i` has `u` points, is closed under `x ↦ 2m − x`
with no fixed point, and two distinct points of `P` have a difference whose
colour is neither `i` nor `c (m + 1)`. -/
theorem endpointNbhd_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) {i : Fin (k + 2)} (hi : i ≠ c (m + 1)) :
    (endpointNbhd c m i).card = u ∧
      (∀ x ∈ endpointNbhd c m i, 2 * m - x ∈ endpointNbhd c m i ∧ 2 * m - x ≠ x) ∧
      ∀ x ∈ endpointNbhd c m i, ∀ y ∈ endpointNbhd c m i, x ≠ y →
        c (Nat.dist x y) ≠ i ∧ c (Nat.dist x y) ≠ c (m + 1) := by
  sorry

/-- **The saturation degree is even.** Under the hypotheses of
`card_centralNbhd_of_frontier`, `u` is even. So if `u` is odd, there is no
Schur colouring of `[1, 2m + 1]` with `k + 2` colours. -/
theorem even_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) : Even u := by
  sorry

/-- **Six colours under `R_4(3) ≤ 61`.** Let `R_4(3) ≤ 61` (a hypothesis), let
`c` be a Schur colouring of `[1, 1801]` with six colours, and let `q = c 901`.
Then each colour occurs 150 times in `[1, 900]`; the central neighbourhood `V`
has 301 points, each with exactly 60 neighbours in `V` of each colour `≠ q`;
`c (901 − d) = c (901 + d)` for every `d ∈ [1, 900]` with `c d = q`; and for
each colour `i ≠ q`, the endpoint neighbourhood of colour `i` has 60 points, is
closed under `x ↦ 1800 − x` with no fixed point, and two distinct points of it
have a difference whose colour is neither `i` nor `q`. This is the case
`k = 4`, `u = 60`, `t = 150`, `m = 900` of the theorems above. It does not
exclude such a colouring. -/
theorem schur_six_frontier_structure (hR : TriangleRamsey 4 61) {c : ℕ → Fin 6}
    (hc : SchurColoring 1801 c) :
    (∀ j, ((Icc 1 900).filter fun d => c d = j).card = 150) ∧
    (centralNbhd c 900).card = 301 ∧
    (∀ v ∈ centralNbhd c 900, ∀ i ≠ c 901, (colorNbhd c (centralNbhd c 900) v i).card = 60) ∧
    (∀ d, 0 < d → d ≤ 900 → c d = c 901 → c (901 - d) = c (901 + d)) ∧
    ∀ i ≠ c 901, (endpointNbhd c 900 i).card = 60 ∧
      (∀ x ∈ endpointNbhd c 900 i, 1800 - x ∈ endpointNbhd c 900 i ∧ 1800 - x ≠ x) ∧
      ∀ x ∈ endpointNbhd c 900 i, ∀ y ∈ endpointNbhd c 900 i, x ≠ y →
        c (Nat.dist x y) ≠ i ∧ c (Nat.dist x y) ≠ c 901 := by
  sorry

end ClassicalSchur

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import ClassicalSchur.SchurBound

/-!
# The frontier of the centred bound: balanced colour classes, saturation and reflection

Let `c` colour `[1, N]` with no monochromatic Schur triple (`SchurColoring`).
Colour the pair `{x, y}` of points of `[0, N]` by `c |x − y|`. Three points
`x < y < z` give the Schur triple `(y − x) + (z − y) = z − x`, so this
difference colouring has no monochromatic triangle (`SchurColoring.not_mono`).

If `k` colours force a monochromatic triangle on `2t + 2` points, the
centred-interval bound of `SchurBound.lean` gives `N ≤ 2(k + 1)t + 1` for
`k + 1` colours. This file studies the frontier `N = 2m + 1`, `m = (k + 1)t`,
from the centre `m`:

* each colour occurs exactly `t` times in `[1, m]`
  (`card_filter_Icc_eq_of_frontier`);
* the two centres `m` and `m + 1` have the same colour degrees
  (`card_colorNbhd_two_centres`).

Then, with `k + 2` colours: if `k` colours force a monochromatic triangle on
`u + 1` points and `2t = (k + 1)u` (so `k + 1` colours force one on
`2t + 2` points), let `m = (k + 2)t` and let `V` be the neighbourhood of the
centre `m` in the colour `q = c (m + 1)` (`centralNbhd`). Then

* `V` has `2t + 1` points, and in `V` each point has exactly `u` neighbours
  of each colour `≠ q` (`card_centralNbhd_of_frontier`,
  `card_colorNbhd_centralNbhd_of_frontier`);
* the reflection `x ↦ 2m − x` fixes the colour of the edges to the endpoint
  `2m + 1`: `c (m + 1 − d) = c (m + 1 + d)` when `c d = q`
  (`color_reflect_of_frontier`). The step is a general lemma on graph
  automorphisms (`color_eq_of_card_filter_eq`);
* the neighbourhood of the endpoint in a colour `i ≠ q` (`endpointNbhd`)
  has `u` points, is closed under the reflection with no fixed point, and has
  no edge of colour `i` or `q` (`endpointNbhd_of_frontier`). So `u` is even
  (`even_of_frontier`).

For six colours with `R_4(3) ≤ 61` (`TriangleRamsey 4 61`, a hypothesis) the
values are `t = 150`, `m = 900`, `u = 60`: `schur_six_frontier_structure`.
A Schur colouring of `[1, 1801]` with six colours gives five sets of 60
points, each closed under `x ↦ 1800 − x` with no fixed point and with
differences in at most four colours. This file does not exclude these sets.
-/

@[expose] public section

namespace ClassicalSchur

open Finset

/-- `c` colours `[1, N]` with no monochromatic Schur triple: there are no
`x, y ≥ 1` with `x + y ≤ N` and `c x = c y = c (x + y)`. The case `x = y` is
included. -/
def SchurColoring {n : ℕ} (N : ℕ) (c : ℕ → Fin n) : Prop :=
  ∀ x y, 0 < x → 0 < y → x + y ≤ N → c x = c y → c (x + y) ≠ c x

/-- A Schur colouring of `[1, N]` with `n` colours gives a cover of `[1, N]`
by `n` sumfree sets. -/
theorem coveredBySumFree_of_schurColoring {n N : ℕ} {c : ℕ → Fin n}
    (hc : SchurColoring N c) : CoveredBySumFree (Set.Icc 1 N) n := by
  refine ⟨fun i => {x | 1 ≤ x ∧ x ≤ N ∧ c x = i}, fun i x hx y hy hxy => ?_, fun x hx => ?_⟩
  · obtain ⟨hx1, -, hxi⟩ := hx
    obtain ⟨hy1, -, hyi⟩ := hy
    obtain ⟨-, hxyN, hxyi⟩ := hxy
    exact hc x y hx1 hy1 hxyN (hxi.trans hyi.symm) (hxyi.trans hxi.symm)
  · exact Set.mem_iUnion.mpr ⟨c x, hx.1, hx.2, rfl⟩

/-- A cover of `[1, N]` by `n ≥ 1` sumfree sets gives a Schur colouring of
`[1, N]` with `n` colours. -/
theorem exists_schurColoring_of_coveredBySumFree {n N : ℕ} (hn : 0 < n)
    (h : CoveredBySumFree (Set.Icc 1 N) n) : ∃ c : ℕ → Fin n, SchurColoring N c := by
  obtain ⟨C, hC, hcov⟩ := h
  have hmem : ∀ x : ℕ, ∃ i : Fin n, 1 ≤ x → x ≤ N → x ∈ C i := by
    intro x
    by_cases hx : 1 ≤ x ∧ x ≤ N
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
      exact ⟨i, fun _ _ => hi⟩
    · exact ⟨⟨0, hn⟩, fun h1 h2 => absurd ⟨h1, h2⟩ hx⟩
  choose c hc using hmem
  refine ⟨c, fun x y hx hy hxy hxy' hsum => ?_⟩
  have m1 := hc x hx (by omega)
  have m2 := hc y hy (by omega)
  have m3 := hc (x + y) (by omega) hxy
  rw [← hxy'] at m2
  rw [hsum] at m3
  exact hC (c x) x m1 y m2 m3

/-- Of three points on a line, one distance is the sum of the other two. -/
private theorem dist_cases (a b w : ℕ) :
    Nat.dist a b + Nat.dist b w = Nat.dist a w ∨
    Nat.dist a b + Nat.dist a w = Nat.dist b w ∨
    Nat.dist a w + Nat.dist b w = Nat.dist a b := by
  unfold Nat.dist
  omega

/-- The difference colouring of a Schur colouring of `[1, N]` has no
monochromatic triangle on three distinct points of `[0, N]`. -/
theorem SchurColoring.not_mono {n N : ℕ} {c : ℕ → Fin n} (hc : SchurColoring N c)
    {a b w : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hw : w ≤ N) (hab : a ≠ b) (haw : a ≠ w)
    (hbw : b ≠ w) (h1 : c (Nat.dist a b) = c (Nat.dist a w))
    (h2 : c (Nat.dist a w) = c (Nat.dist b w)) : False := by
  have pab := Nat.dist_pos_of_ne hab
  have paw := Nat.dist_pos_of_ne haw
  have pbw := Nat.dist_pos_of_ne hbw
  have lab : Nat.dist a b ≤ N := by unfold Nat.dist; omega
  have law : Nat.dist a w ≤ N := by unfold Nat.dist; omega
  have lbw : Nat.dist b w ≤ N := by unfold Nat.dist; omega
  rcases dist_cases a b w with h | h | h
  · exact hc _ _ pab pbw (by omega) (h1.trans h2) (by rw [h]; exact h1.symm)
  · exact hc _ _ pab paw (by omega) h1 (by rw [h]; exact (h1.trans h2).symm)
  · exact hc _ _ paw pbw (by omega) h2 (by rw [h]; exact h1)

/-- If the differences of the points of `V ⊆ [0, N]` take their colours in a
set `K` of at most `k` colours, and `k` colours force a monochromatic triangle
on `r` points, then `V` has fewer than `r` points. -/
theorem SchurColoring.card_lt {n N k r : ℕ} {c : ℕ → Fin n} (hc : SchurColoring N c)
    (hR : TriangleRamsey k r) {V : Finset ℕ} (hV : ∀ x ∈ V, x ≤ N) {K : Finset (Fin n)}
    (hK : K.card ≤ k) (hcol : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → c (Nat.dist x y) ∈ K) :
    V.card < r := by
  by_contra hr
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, e1, e2⟩ :=
    hR V (K.image Fin.val) (fun x y => (c (Nat.dist x y) : ℕ)) (card_image_le.trans hK)
      (not_lt.mp hr) (fun x hx y hy hxy => mem_image_of_mem _ (hcol x hx y hy hxy.ne))
  exact hc.not_mono (hV x hx) (hV y hy) (hV z hz) hxy.ne (by omega) hyz.ne (Fin.ext e2)
    ((Fin.ext e2).symm.trans (Fin.ext e1))

/-- The colour-`i` neighbourhood of `v` in `V` for the difference colouring of
`c`: the points `w ≠ v` of `V` with `c |v − w| = i`. -/
def colorNbhd {n : ℕ} (c : ℕ → Fin n) (V : Finset ℕ) (v : ℕ) (i : Fin n) : Finset ℕ :=
  (V.erase v).filter fun w => c (Nat.dist v w) = i

/-- Membership in a colour neighbourhood. -/
theorem mem_colorNbhd {n : ℕ} {c : ℕ → Fin n} {V : Finset ℕ} {v w : ℕ} {i : Fin n} :
    w ∈ colorNbhd c V v i ↔ w ≠ v ∧ w ∈ V ∧ c (Nat.dist v w) = i := by
  simp [colorNbhd, and_assoc]

/-- The degrees of `v` in the colours sum to the number of other points of `V`. -/
theorem sum_card_colorNbhd {n : ℕ} (c : ℕ → Fin n) (V : Finset ℕ) (v : ℕ) :
    ∑ i, (colorNbhd c V v i).card = (V.erase v).card :=
  (card_eq_sum_card_fiberwise fun w _ => mem_univ (c (Nat.dist v w))).symm

/-- Two points of a colour-`i` neighbourhood are not joined in colour `i`. -/
theorem SchurColoring.color_ne_of_mem_colorNbhd {n N : ℕ} {c : ℕ → Fin n}
    (hc : SchurColoring N c) {V : Finset ℕ} (hV : ∀ x ∈ V, x ≤ N) {v : ℕ} (hv : v ≤ N)
    {i : Fin n} {x y : ℕ} (hx : x ∈ colorNbhd c V v i) (hy : y ∈ colorNbhd c V v i)
    (hxy : x ≠ y) : c (Nat.dist x y) ≠ i := by
  intro h
  obtain ⟨hxv, hxV, hxi⟩ := mem_colorNbhd.mp hx
  obtain ⟨hyv, hyV, hyi⟩ := mem_colorNbhd.mp hy
  exact hc.not_mono hv (hV x hxV) (hV y hyV) (Ne.symm hxv) (Ne.symm hyv) hxy
    (hxi.trans hyi.symm) (hyi.trans h.symm)

/-- If `|s|` numbers, each at most `b`, sum to `|s| · b`, then each is `b`. -/
private theorem eq_of_sum_eq_card_mul {ι : Type*} {s : Finset ι} {f : ι → ℕ} {b : ℕ}
    (hle : ∀ i ∈ s, f i ≤ b) (hsum : ∑ i ∈ s, f i = s.card * b) : ∀ i ∈ s, f i = b := by
  intro i hi
  by_contra hne
  have hlt : ∑ j ∈ s, f j < ∑ _j ∈ s, b :=
    sum_lt_sum hle ⟨i, hi, lt_of_le_of_ne (hle i hi) hne⟩
  rw [sum_const, smul_eq_mul] at hlt
  omega

/-- **Two centres.** The reflection `x ↦ N − x` of `[0, N]` keeps all
differences, so `v` and `N − v` have the same number of neighbours of each
colour. -/
theorem card_colorNbhd_range_reflect {n : ℕ} (c : ℕ → Fin n) {N v : ℕ} (hv : v ≤ N)
    (i : Fin n) :
    (colorNbhd c (range (N + 1)) (N - v) i).card = (colorNbhd c (range (N + 1)) v i).card := by
  apply card_nbij' (fun x => N - x) (fun x => N - x)
  · intro x hx
    obtain ⟨hxv, hxr, hxi⟩ := mem_colorNbhd.mp hx
    rw [mem_range] at hxr
    change N - x ∈ colorNbhd c (range (N + 1)) v i
    refine mem_colorNbhd.mpr ⟨by omega, mem_range.mpr (by omega), ?_⟩
    rwa [show Nat.dist v (N - x) = Nat.dist (N - v) x by unfold Nat.dist; omega]
  · intro x hx
    obtain ⟨hxv, hxr, hxi⟩ := mem_colorNbhd.mp hx
    rw [mem_range] at hxr
    change N - x ∈ colorNbhd c (range (N + 1)) (N - v) i
    refine mem_colorNbhd.mpr ⟨by omega, mem_range.mpr (by omega), ?_⟩
    rwa [show Nat.dist (N - v) (N - x) = Nat.dist v x by unfold Nat.dist; omega]
  · intro x hx
    have := mem_range.mp (mem_colorNbhd.mp hx).2.1
    change N - (N - x) = x
    omega
  · intro x hx
    have := mem_range.mp (mem_colorNbhd.mp hx).2.1
    change N - (N - x) = x
    omega

/-- **Two centres** of `[0, 2m + 1]`: `m` and `m + 1` have the same number of
neighbours of each colour. -/
theorem card_colorNbhd_two_centres {n : ℕ} (c : ℕ → Fin n) (m : ℕ) (i : Fin n) :
    (colorNbhd c (range (2 * m + 2)) (m + 1) i).card =
      (colorNbhd c (range (2 * m + 2)) m i).card := by
  have h := card_colorNbhd_range_reflect c (N := 2 * m + 1) (v := m) (by omega) i
  rwa [show 2 * m + 1 - m = m + 1 by omega] at h

/-- The points `m ± d` for `d ∈ [1, m]` with `c d = j` lie in the colour-`j`
neighbourhood of the centre `m` of `[0, 2m + 1]`, and are not the endpoint. -/
private theorem two_mul_card_le_card_colorNbhd {n : ℕ} (c : ℕ → Fin n) (m : ℕ) (j : Fin n) :
    2 * ((Icc 1 m).filter fun d => c d = j).card ≤
      ((colorNbhd c (range (2 * m + 2)) m j).erase (2 * m + 1)).card := by
  set D := (Icc 1 m).filter fun d => c d = j with hD
  have hDm : ∀ d ∈ D, 1 ≤ d ∧ d ≤ m ∧ c d = j := by
    intro d hd
    obtain ⟨h1, h2⟩ := mem_filter.mp hd
    exact ⟨(mem_Icc.mp h1).1, (mem_Icc.mp h1).2, h2⟩
  have hsub : D.image (fun d => m - d) ∪ D.image (fun d => m + d) ⊆
      (colorNbhd c (range (2 * m + 2)) m j).erase (2 * m + 1) := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨d, hd, rfl⟩ := mem_image.mp hx
      obtain ⟨h1, h2, h3⟩ := hDm d hd
      refine mem_erase.mpr ⟨by omega, mem_colorNbhd.mpr ⟨by omega, mem_range.mpr (by omega), ?_⟩⟩
      rwa [show Nat.dist m (m - d) = d by unfold Nat.dist; omega]
    · obtain ⟨d, hd, rfl⟩ := mem_image.mp hx
      obtain ⟨h1, h2, h3⟩ := hDm d hd
      refine mem_erase.mpr ⟨by omega, mem_colorNbhd.mpr ⟨by omega, mem_range.mpr (by omega), ?_⟩⟩
      rwa [show Nat.dist m (m + d) = d by unfold Nat.dist; omega]
  have hinj1 : Set.InjOn (fun d => m - d) D := by
    intro a ha b hb hab
    have := hDm a ha
    have := hDm b hb
    simp only at hab
    omega
  have hinj2 : Set.InjOn (fun d => m + d) D := by
    intro a _ b _ hab
    simp only at hab
    omega
  have hdisj : Disjoint (D.image fun d => m - d) (D.image fun d => m + d) := by
    rw [disjoint_left]
    intro x hx1 hx2
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx1
    obtain ⟨b, hb, hab⟩ := mem_image.mp hx2
    have := hDm a ha
    have := hDm b hb
    omega
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_image_of_injOn hinj1, card_image_of_injOn hinj2] at this
  omega

/-- **Balanced colour classes at the frontier.** If `k` colours force a
monochromatic triangle on `2t + 2` points and `c` is a Schur colouring of
`[1, 2m + 1]` with `k + 1` colours, `m = (k + 1)t` (the largest interval that
the centred bound allows), then each colour occurs exactly `t` times in
`[1, m]`. -/
theorem card_filter_Icc_eq_of_frontier {k t m : ℕ} (hR : TriangleRamsey k (2 * t + 2))
    (hm : m = (k + 1) * t) {c : ℕ → Fin (k + 1)} (hc : SchurColoring (2 * m + 1) c)
    (j : Fin (k + 1)) : ((Icc 1 m).filter fun d => c d = j).card = t := by
  have hrange : ∀ x ∈ range (2 * m + 2), x ≤ 2 * m + 1 := fun x hx => by
    have := mem_range.mp hx
    omega
  have hle : ∀ j : Fin (k + 1), ((Icc 1 m).filter fun d => c d = j).card ≤ t := by
    intro j
    have h2 := two_mul_card_le_card_colorNbhd c m j
    have hP : (colorNbhd c (range (2 * m + 2)) m j).card < 2 * t + 2 := by
      refine hc.card_lt hR (fun x hx => hrange x (mem_colorNbhd.mp hx).2.1)
        (K := univ.erase j) (by simp) fun x hx y hy hxy => ?_
      exact mem_erase.mpr
        ⟨hc.color_ne_of_mem_colorNbhd hrange (by omega) hx hy hxy, mem_univ _⟩
    have := card_erase_le (s := colorNbhd c (range (2 * m + 2)) m j) (a := 2 * m + 1)
    omega
  have hsum : ∑ j, ((Icc 1 m).filter fun d => c d = j).card =
      (univ : Finset (Fin (k + 1))).card * t := by
    rw [← card_eq_sum_card_fiberwise fun d _ => mem_univ (c d), Nat.card_Icc, card_univ,
      Fintype.card_fin, hm]
    omega
  exact eq_of_sum_eq_card_mul (fun j _ => hle j) hsum j (mem_univ j)

/-- `k + 1` colours force a monochromatic triangle on `(k + 1)u + 2` points
when `k` colours force one on `u + 1` points. -/
private theorem triangleRamsey_of_two_mul {k u t : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) : TriangleRamsey (k + 1) (2 * t + 2) := by
  have h := triangleRamsey_succ hR
  rwa [Nat.add_sub_cancel, ← h2t] at h

/-- The neighbourhood of the centre `m` of `[0, 2m + 1]` in the colour
`c (m + 1)` of its edge to the endpoint `2m + 1`. -/
def centralNbhd {n : ℕ} (c : ℕ → Fin n) (m : ℕ) : Finset ℕ :=
  colorNbhd c (range (2 * m + 2)) m (c (m + 1))

/-- Membership in the central neighbourhood: `x ∈ [0, 2m + 1]`, `x ≠ m`, and
`c |m − x| = c (m + 1)`. -/
theorem mem_centralNbhd {n : ℕ} {c : ℕ → Fin n} {m x : ℕ} :
    x ∈ centralNbhd c m ↔ x ≠ m ∧ x ≤ 2 * m + 1 ∧ c (Nat.dist m x) = c (m + 1) := by
  rw [centralNbhd, mem_colorNbhd, mem_range, Nat.lt_succ_iff]

/-- The endpoint `2m + 1` is in the central neighbourhood, since
`(2m + 1) − m = m + 1`. -/
theorem endpoint_mem_centralNbhd {n : ℕ} (c : ℕ → Fin n) (m : ℕ) :
    2 * m + 1 ∈ centralNbhd c m :=
  mem_centralNbhd.mpr ⟨by omega, le_rfl, by rw [show Nat.dist m (2 * m + 1) = m + 1 by
    unfold Nat.dist; omega]⟩

/-- No two points of the central neighbourhood are joined in its colour. -/
theorem SchurColoring.color_ne_of_mem_centralNbhd {n m : ℕ} {c : ℕ → Fin n}
    (hc : SchurColoring (2 * m + 1) c) {x y : ℕ} (hx : x ∈ centralNbhd c m)
    (hy : y ∈ centralNbhd c m) (hxy : x ≠ y) : c (Nat.dist x y) ≠ c (m + 1) :=
  hc.color_ne_of_mem_colorNbhd (fun z hz => Nat.lt_succ_iff.mp (mem_range.mp hz)) (by omega)
    hx hy hxy

/-- **The central neighbourhood at the frontier** has `2t + 1` points. -/
theorem card_centralNbhd_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) : (centralNbhd c m).card = 2 * t + 1 := by
  have hR' := triangleRamsey_of_two_mul hR h2t
  have hD : ((Icc 1 m).filter fun d => c d = c (m + 1)).card = t :=
    card_filter_Icc_eq_of_frontier hR' (by rw [hm]) hc (c (m + 1))
  have h2 := two_mul_card_le_card_colorNbhd c m (c (m + 1))
  have hN := card_erase_add_one (endpoint_mem_centralNbhd c m)
  have hlt : (centralNbhd c m).card < 2 * t + 2 := by
    refine hc.card_lt hR' (fun x hx => (mem_centralNbhd.mp hx).2.1) (K := univ.erase (c (m + 1)))
      (by simp) fun x hx y hy hxy => ?_
    exact mem_erase.mpr ⟨hc.color_ne_of_mem_centralNbhd hx hy hxy, mem_univ _⟩
  unfold centralNbhd at hN hlt ⊢
  omega

/-- **Nested saturation.** At the frontier, each point of the central
neighbourhood `V` has exactly `u` neighbours in `V` of each colour `i ≠ q`:
`V` has no edge of colour `q`, a neighbourhood of colour `i` in `V` uses at
most `k` colours, so it has at most `u` points, and the `k + 1` degrees sum
to `|V| − 1 = 2t = (k + 1)u`. -/
theorem card_colorNbhd_centralNbhd_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) {v : ℕ} (hv : v ∈ centralNbhd c m) {i : Fin (k + 2)}
    (hi : i ≠ c (m + 1)) : (colorNbhd c (centralNbhd c m) v i).card = u := by
  set V := centralNbhd c m with hV
  set q := c (m + 1) with hq
  have hVN : ∀ x ∈ V, x ≤ 2 * m + 1 := fun x hx => (mem_centralNbhd.mp hx).2.1
  have hvN := hVN v hv
  -- each degree of colour `≠ q` is at most `u`
  have hle : ∀ j ∈ univ.erase q, (colorNbhd c V v j).card ≤ u := by
    intro j hj
    have hjq : j ≠ q := ne_of_mem_erase hj
    have hlt : (colorNbhd c V v j).card < u + 1 := by
      refine hc.card_lt hR (fun x hx => hVN x (mem_colorNbhd.mp hx).2.1)
        (K := (univ.erase j).erase q) ?_ fun x hx y hy hxy => ?_
      · rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hjq, mem_univ _⟩),
          card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
        omega
      · refine mem_erase.mpr ⟨hc.color_ne_of_mem_centralNbhd (mem_colorNbhd.mp hx).2.1
          (mem_colorNbhd.mp hy).2.1 hxy, mem_erase.mpr ⟨?_, mem_univ _⟩⟩
        exact hc.color_ne_of_mem_colorNbhd hVN hvN hx hy hxy
    omega
  -- the degree of colour `q` is `0`
  have hzero : (colorNbhd c V v q).card = 0 := by
    rw [card_eq_zero, eq_empty_iff_forall_notMem]
    intro w hw
    obtain ⟨hwv, hwV, hwq⟩ := mem_colorNbhd.mp hw
    exact hc.color_ne_of_mem_centralNbhd hv hwV (Ne.symm hwv) hwq
  -- the degrees sum to `2t = (k + 1)u`
  have hcard := card_centralNbhd_of_frontier hR h2t hm hc
  have hsum : ∑ j ∈ univ.erase q, (colorNbhd c V v j).card = (univ.erase q).card * u := by
    rw [sum_erase (f := fun j => (colorNbhd c V v j).card) univ hzero, sum_card_colorNbhd,
      card_erase_of_mem hv, hV, hcard,
      card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    rw [Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega, h2t]
  exact eq_of_sum_eq_card_mul hle hsum i (mem_erase.mpr ⟨hi, mem_univ _⟩)

/-- **Automorphism extension.** Let `J` be an involution of `W` that keeps the
colours `col` of all pairs in `W`, and let `e ∉ W`. If `v ∈ W` and `J v` have
the same number of neighbours of each colour in `W ∪ {e}`, then the edges
`v e` and `J v e` have the same colour: the neighbours in `W` match by `J`,
so the edges to `e` must match too. -/
theorem color_eq_of_card_filter_eq {α γ : Type*} [DecidableEq α] [DecidableEq γ]
    (col : α → α → γ) {W : Finset α} {e : α} (he : e ∉ W) (J : α → α)
    (hJ : ∀ x ∈ W, J x ∈ W) (hJJ : ∀ x ∈ W, J (J x) = x)
    (hcol : ∀ x ∈ W, ∀ y ∈ W, col (J x) (J y) = col x y) {v : α} (hv : v ∈ W)
    (hdeg : ∀ i, (((insert e W).erase v).filter fun w => col v w = i).card =
      (((insert e W).erase (J v)).filter fun w => col (J v) w = i).card) :
    col v e = col (J v) e := by
  have hJv := hJ v hv
  -- the neighbours in `W` correspond by `J`
  have hW : ∀ i, ((W.erase v).filter fun w => col v w = i).card =
      ((W.erase (J v)).filter fun w => col (J v) w = i).card := by
    intro i
    apply card_nbij' J J
    · intro w hw
      obtain ⟨hw1, hw2⟩ := mem_filter.mp hw
      obtain ⟨hwv, hwW⟩ := mem_erase.mp hw1
      refine mem_filter.mpr ⟨mem_erase.mpr ⟨fun h => hwv ?_, hJ w hwW⟩, ?_⟩
      · rw [← hJJ w hwW, h, hJJ v hv]
      · rw [hcol v hv w hwW]
        exact hw2
    · intro w hw
      obtain ⟨hw1, hw2⟩ := mem_filter.mp hw
      obtain ⟨hwv, hwW⟩ := mem_erase.mp hw1
      refine mem_filter.mpr ⟨mem_erase.mpr ⟨fun h => hwv ?_, hJ w hwW⟩, ?_⟩
      · rw [← h, hJJ w hwW]
      · rw [← hJJ v hv, hcol (J v) hJv w hwW]
        exact hw2
    · intro w hw
      exact hJJ w (mem_erase.mp (mem_filter.mp hw).1).2
    · intro w hw
      exact hJJ w (mem_erase.mp (mem_filter.mp hw).1).2
  have hev : e ≠ v := fun h => he (h ▸ hv)
  have heJv : e ≠ J v := fun h => he (h ▸ hJv)
  have h := hdeg (col v e)
  rw [erase_insert_of_ne hev, erase_insert_of_ne heJv, filter_insert, filter_insert,
    ite_eq_left rfl, card_insert_of_notMem (fun h => he (mem_of_mem_erase (mem_filter.mp h).1))] at h
  by_contra hne
  rw [ite_eq_right (Ne.symm hne), hW] at h
  omega

/-- The reflection `x ↦ 2m − x` maps the central neighbourhood without its
endpoint to itself. -/
theorem reflect_mem_centralNbhd {n : ℕ} {c : ℕ → Fin n} {m x : ℕ}
    (hx : x ∈ centralNbhd c m) (hxN : x ≠ 2 * m + 1) :
    2 * m - x ∈ centralNbhd c m ∧ 2 * m - x ≠ 2 * m + 1 := by
  obtain ⟨hxm, hxle, hxq⟩ := mem_centralNbhd.mp hx
  refine ⟨mem_centralNbhd.mpr ⟨by omega, by omega, ?_⟩, by omega⟩
  rwa [show Nat.dist m (2 * m - x) = Nat.dist m x by unfold Nat.dist; omega]

/-- **Forced reflection at the frontier.** If `d ∈ [1, m]` has the colour
`q = c (m + 1)`, then `c (m + 1 − d) = c (m + 1 + d)`. -/
theorem color_reflect_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) {d : ℕ} (hd : 0 < d) (hdm : d ≤ m)
    (hq : c d = c (m + 1)) : c (m + 1 - d) = c (m + 1 + d) := by
  set V := centralNbhd c m with hV
  set N := 2 * m + 1 with hN
  have hNV : N ∈ V := endpoint_mem_centralNbhd c m
  have hVN : ∀ x ∈ V, x ≤ N := fun x hx => (mem_centralNbhd.mp hx).2.1
  have hmdV : m + d ∈ V.erase N := by
    refine mem_erase.mpr ⟨by omega, mem_centralNbhd.mpr ⟨by omega, by omega, ?_⟩⟩
    rwa [show Nat.dist m (m + d) = d by unfold Nat.dist; omega]
  have hmem : ∀ x ∈ V.erase N, x ∈ V ∧ x ≤ 2 * m := fun x hx =>
    ⟨mem_of_mem_erase hx, by have := hVN x (mem_of_mem_erase hx); have := ne_of_mem_erase hx; omega⟩
  have key := color_eq_of_card_filter_eq (fun x y => c (Nat.dist x y)) (W := V.erase N) (e := N)
    (notMem_erase N V) (fun x => 2 * m - x)
    (fun x hx => by
      obtain ⟨h1, h2⟩ := reflect_mem_centralNbhd (mem_of_mem_erase hx) (ne_of_mem_erase hx)
      exact mem_erase.mpr ⟨h2, h1⟩)
    (fun x hx => by have := (hmem x hx).2; omega)
    (fun x hx y hy => by
      have := (hmem x hx).2
      have := (hmem y hy).2
      rw [show Nat.dist (2 * m - x) (2 * m - y) = Nat.dist x y by unfold Nat.dist; omega])
    hmdV (fun i => by
      rw [insert_erase hNV]
      have hv1 : m + d ∈ V := mem_of_mem_erase hmdV
      have hv2 : 2 * m - (m + d) ∈ V :=
        (reflect_mem_centralNbhd hv1 (ne_of_mem_erase hmdV)).1
      change (colorNbhd c V (m + d) i).card = (colorNbhd c V (2 * m - (m + d)) i).card
      by_cases hi : i = c (m + 1)
      · have hz : ∀ v ∈ V, (colorNbhd c V v i).card = 0 := by
          intro v hv
          rw [card_eq_zero, eq_empty_iff_forall_notMem]
          intro w hw
          obtain ⟨hwv, hwV, hwi⟩ := mem_colorNbhd.mp hw
          exact hc.color_ne_of_mem_centralNbhd hv hwV (Ne.symm hwv) (hwi.trans hi)
        rw [hz _ hv1, hz _ hv2]
      · rw [card_colorNbhd_centralNbhd_of_frontier hR h2t hm hc hv1 hi,
          card_colorNbhd_centralNbhd_of_frontier hR h2t hm hc hv2 hi])
  rwa [show Nat.dist (m + d) N = m + 1 - d by unfold Nat.dist; omega,
    show Nat.dist (2 * m - (m + d)) N = m + 1 + d by unfold Nat.dist; omega] at key

/-- The neighbourhood of the endpoint `2m + 1` of colour `i` inside the
central neighbourhood. -/
def endpointNbhd {n : ℕ} (c : ℕ → Fin n) (m : ℕ) (i : Fin n) : Finset ℕ :=
  colorNbhd c (centralNbhd c m) (2 * m + 1) i

/-- **Paired endpoint neighbourhoods.** At the frontier, for each colour
`i ≠ q`, the endpoint neighbourhood `P` of colour `i` has `u` points, is
closed under the reflection `x ↦ 2m − x` with no fixed point, and has no
difference of colour `i` or `q`. -/
theorem endpointNbhd_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) {i : Fin (k + 2)} (hi : i ≠ c (m + 1)) :
    (endpointNbhd c m i).card = u ∧
      (∀ x ∈ endpointNbhd c m i, 2 * m - x ∈ endpointNbhd c m i ∧ 2 * m - x ≠ x) ∧
      ∀ x ∈ endpointNbhd c m i, ∀ y ∈ endpointNbhd c m i, x ≠ y →
        c (Nat.dist x y) ≠ i ∧ c (Nat.dist x y) ≠ c (m + 1) := by
  have hNV := endpoint_mem_centralNbhd c m
  refine ⟨card_colorNbhd_centralNbhd_of_frontier hR h2t hm hc hNV hi, fun x hx => ?_,
    fun x hx y hy hxy => ⟨?_, ?_⟩⟩
  · obtain ⟨hxN, hxV, hxi⟩ := mem_colorNbhd.mp hx
    obtain ⟨hxm, hxle, hxq⟩ := mem_centralNbhd.mp hxV
    obtain ⟨hJV, hJN⟩ := reflect_mem_centralNbhd hxV hxN
    refine ⟨mem_colorNbhd.mpr ⟨hJN, hJV, ?_⟩, by omega⟩
    have hd : c (Nat.dist m x) = c (m + 1) := hxq
    have key := color_reflect_of_frontier hR h2t hm hc (d := Nat.dist m x)
      (Nat.dist_pos_of_ne (Ne.symm hxm)) (by unfold Nat.dist; omega) hd
    rcases le_or_gt x m with hle | hlt
    · rw [show Nat.dist m x = m - x by unfold Nat.dist; omega] at key
      rw [show Nat.dist (2 * m + 1) x = m + 1 + (m - x) by unfold Nat.dist; omega] at hxi
      rw [show Nat.dist (2 * m + 1) (2 * m - x) = m + 1 - (m - x) by unfold Nat.dist; omega,
        key, hxi]
    · rw [show Nat.dist m x = x - m by unfold Nat.dist; omega] at key
      rw [show Nat.dist (2 * m + 1) x = m + 1 - (x - m) by unfold Nat.dist; omega] at hxi
      rw [show Nat.dist (2 * m + 1) (2 * m - x) = m + 1 + (x - m) by unfold Nat.dist; omega,
        ← key, hxi]
  · exact hc.color_ne_of_mem_colorNbhd (fun z hz => (mem_centralNbhd.mp hz).2.1) le_rfl hx hy hxy
  · exact hc.color_ne_of_mem_centralNbhd (mem_colorNbhd.mp hx).2.1 (mem_colorNbhd.mp hy).2.1 hxy

/-- **The saturation degree is even.** At the frontier, `u` is even: an
endpoint neighbourhood has `u` points and is closed under the reflection
`x ↦ 2m − x` with no fixed point, so its points below `m` and above `m` are
paired. -/
theorem even_of_frontier {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) : Even u := by
  obtain ⟨i, hi⟩ := exists_ne (c (m + 1))
  obtain ⟨hcard, hrefl, -⟩ := endpointNbhd_of_frontier hR h2t hm hc hi
  set P := endpointNbhd c m i with hP
  have hle : ∀ x ∈ P, x ≤ 2 * m := fun x hx => by
    obtain ⟨hxN, hxV, -⟩ := mem_colorNbhd.mp hx
    have := (mem_centralNbhd.mp hxV).2.1
    omega
  have hhalf : (P.filter fun x => ¬ x < m).card = (P.filter fun x => x < m).card := by
    apply card_nbij' (fun x => 2 * m - x) (fun x => 2 * m - x)
    · intro x hx
      obtain ⟨hxP, hxm⟩ := mem_filter.mp hx
      obtain ⟨hJ, hJx⟩ := hrefl x hxP
      have := hle x hxP
      change 2 * m - x ∈ P.filter fun x => x < m
      exact mem_filter.mpr ⟨hJ, by omega⟩
    · intro x hx
      obtain ⟨hxP, hxm⟩ := mem_filter.mp hx
      obtain ⟨hJ, -⟩ := hrefl x hxP
      change 2 * m - x ∈ P.filter fun x => ¬ x < m
      exact mem_filter.mpr ⟨hJ, by omega⟩
    · intro x hx
      have := hle x (mem_filter.mp hx).1
      change 2 * m - (2 * m - x) = x
      omega
    · intro x hx
      have := hle x (mem_filter.mp hx).1
      change 2 * m - (2 * m - x) = x
      omega
  have hsplit := card_filter_add_card_filter_not (s := P) fun x => x < m
  exact ⟨(P.filter fun x => x < m).card, by omega⟩

/-- If `u` is odd, no Schur colouring of the frontier interval `[1, 2m + 1]`
with `k + 2` colours exists. -/
theorem not_schurColoring_frontier_of_odd {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) (hu : Odd u) (c : ℕ → Fin (k + 2)) :
    ¬ SchurColoring (2 * m + 1) c := fun hc =>
  Nat.not_even_iff_odd.mpr hu (even_of_frontier hR h2t hm hc)

/-- **Six colours with `R_4(3) ≤ 61`.** Let `c` be a Schur colouring of
`[1, 1801]` with six colours, so `S(6) ≥ 1801`, and let `q = c 901`. If four
colours force a monochromatic triangle on 61 points, then:
each colour occurs 150 times in `[1, 900]`; the neighbourhood `V` of `900` in
colour `q` has 301 points, each with exactly 60 neighbours in `V` of each
colour `≠ q`; `c (901 − d) = c (901 + d)` whenever `d ∈ [1, 900]` has colour
`q`; and for each colour `i ≠ q`, the neighbourhood of `1801` in `V` of colour
`i` has 60 points, is closed under `x ↦ 1800 − x` with no fixed point, and has
no difference of colour `i` or `q`. -/
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
  have hR' : TriangleRamsey 4 (60 + 1) := hR
  have h2t : 2 * 150 = (4 + 1) * 60 := by norm_num
  have hm : 900 = (4 + 2) * 150 := by norm_num
  have hc' : SchurColoring (2 * 900 + 1) c := hc
  exact ⟨card_filter_Icc_eq_of_frontier (triangleRamsey_of_two_mul hR' h2t) hm hc',
    card_centralNbhd_of_frontier hR' h2t hm hc',
    fun v hv i hi => card_colorNbhd_centralNbhd_of_frontier hR' h2t hm hc' hv hi,
    fun d hd hdm hq => color_reflect_of_frontier hR' h2t hm hc' hd hdm hq,
    fun i hi => endpointNbhd_of_frontier hR' h2t hm hc' hi⟩

end ClassicalSchur

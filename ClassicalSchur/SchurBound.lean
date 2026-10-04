/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import ClassicalSchur.Ramsey

/-!
# Schur bounds from triangle Ramsey bounds: the centred interval

If every colouring with `k` colours of the pairs of `r` points has a
monochromatic triangle, then `[1, 2(k + 1)⌊(r − 1)/2⌋ + 2]` is not covered by
`k + 1` sumfree sets. In the usual notation: `R_k(3) ≤ r` implies
`S(k + 1) ≤ 2(k + 1)⌊(r − 1)/2⌋ + 1`.

Proof. Put `q = ⌊(r − 1)/2⌋` and `h = (k + 1)q + 1`. One set `C_i` of the cover
holds at least `q + 1` elements `a` of `[1, h]`. The points `h ± a` are
`2q + 2 ≥ r` points of `[0, 2h]`. Colour a pair `x < y` of them by the cover
set of `y − x`. No difference is in `C_i`: `(h + b) − (h − a) = a + b`, and
the other differences are `a − b` with `b < a` and `(a − b) + b = a`. So at
most `k` colours occur, and a monochromatic triangle `x < y < z` puts
`y − x`, `z − y` and their sum `z − x` in one sumfree set.

With `R_4(3) ≤ 61`, one step of the pigeonhole recursion gives
`R_5(3) ≤ 302` and then `S(6) ≤ 1801`. Here `R_4(3) ≤ 61` is a hypothesis:
it is a computer-assisted claim of M. Tatarevic (2026,
https://github.com/milostatarevic/r3333-upper-bound). The published bound is
`R_4(3) ≤ 62`. With `R_2(3) ≤ 6` the bound gives `S(3) ≤ 13`, which is exact.
-/

@[expose] public section

namespace ClassicalSchur

/-- One step of the pigeonhole recursion: `TriangleRamsey k N` implies
`TriangleRamsey (k + 1) ((k + 1)(N − 1) + 2)`. -/
theorem triangleRamsey_succ {k N : ℕ} (hR : TriangleRamsey k N) :
    TriangleRamsey (k + 1) ((k + 1) * (N - 1) + 2) := by
  intro V K c hK hV hc
  have hVne : V.Nonempty := by rw [← Finset.card_pos]; omega
  set v := V.min' hVne with hv
  have hvV : v ∈ V := V.min'_mem hVne
  set W := V.erase v with hW
  have hWcard : (k + 1) * (N - 1) + 1 ≤ W.card := by
    rw [hW, Finset.card_erase_of_mem hvV]
    omega
  have hvW : ∀ w ∈ W, v < w := fun w hw =>
    lt_of_le_of_ne (V.min'_le w (Finset.mem_of_mem_erase hw)) (Finset.ne_of_mem_erase hw).symm
  have hmaps : ∀ w ∈ W, c v w ∈ K := fun w hw =>
    hc v hvV w (Finset.mem_of_mem_erase hw) (hvW w hw)
  have hlt : K.card * (N - 1) < W.card :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hK) (by omega)
  obtain ⟨i, hiK, hi⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
  set U := W.filter fun w => c v w = i with hU
  have hUV : U ⊆ V := fun u hu => Finset.mem_of_mem_erase (Finset.mem_filter.mp hu).1
  by_cases hmono : ∃ x ∈ U, ∃ y ∈ U, x < y ∧ c x y = i
  · obtain ⟨x, hx, y, hy, hxy, hcxy⟩ := hmono
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    exact ⟨v, hvV, x, hUV hx, y, hUV hy, hvW x hx'.1, hxy, by rw [hx'.2, hcxy],
      by rw [hx'.2, hy'.2]⟩
  · push Not at hmono
    obtain ⟨x, hx, y, hy, z, hz, h1, h2, h3, h4⟩ := hR U (K.erase i) c
      (by rw [Finset.card_erase_of_mem hiK]; omega) (by omega)
      (fun x hx y hy hxy =>
        Finset.mem_erase.mpr ⟨hmono x hx y hy hxy, hc x (hUV hx) y (hUV hy) hxy⟩)
    exact ⟨x, hUV hx, y, hUV hy, z, hUV hz, h1, h2, h3, h4⟩

/-- The centred-interval bound: if `k` colours force a monochromatic triangle
on `r` points, then `[1, 2((k + 1)⌊(r − 1)/2⌋ + 1)]` is not covered by `k + 1`
sumfree sets, so `S(k + 1) ≤ 2(k + 1)⌊(r − 1)/2⌋ + 1`. -/
theorem not_coveredBySumFree_Icc_of_triangleRamsey {k r : ℕ} (hR : TriangleRamsey k r) :
    ¬ CoveredBySumFree (Set.Icc 1 (2 * ((k + 1) * ((r - 1) / 2) + 1))) (k + 1) := by
  classical
  rintro ⟨C, hC, hcov⟩
  set q := (r - 1) / 2 with hq
  set h := (k + 1) * q + 1 with hh
  -- a cover set for every element of `[1, 2h]`
  have hmem : ∀ n : ℕ, ∃ t : Fin (k + 1), 1 ≤ n → n ≤ 2 * h → n ∈ C t := by
    intro n
    by_cases hn : 1 ≤ n ∧ n ≤ 2 * h
    · obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (hcov ⟨hn.1, hn.2⟩)
      exact ⟨t, fun _ _ => ht⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hn⟩
  choose f hf using hmem
  -- one cover set holds `q + 1` elements of `[1, h]`
  have hmaps : ∀ a ∈ Finset.Icc 1 h, f a ∈ (Finset.univ : Finset (Fin (k + 1))) :=
    fun a _ => Finset.mem_univ _
  have hlt : (Finset.univ : Finset (Fin (k + 1))).card * q < (Finset.Icc 1 h).card := by
    rw [Finset.card_univ, Fintype.card_fin, Nat.card_Icc]
    omega
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
  set A := (Finset.Icc 1 h).filter fun a => f a = i with hA
  have hAC : ∀ a ∈ A, 1 ≤ a ∧ a ≤ h ∧ a ∈ C i := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha1
    refine ⟨h1, h2, ?_⟩
    have := hf a h1 (by omega)
    rwa [ha2] at this
  -- the points `h ± a`
  set V := A.image (fun a => h - a) ∪ A.image (fun a => h + a) with hV
  have hinj1 : Set.InjOn (fun a => h - a) A := by
    intro a ha b hb hab
    have hab' : h - a = h - b := hab
    have := hAC a ha
    have := hAC b hb
    omega
  have hinj2 : Set.InjOn (fun a => h + a) A := by
    intro a _ b _ hab
    have hab' : h + a = h + b := hab
    omega
  have hdisj : Disjoint (A.image (fun a => h - a)) (A.image (fun a => h + a)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx1
    obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hx2
    have hax' : h - a = x := hax
    have hbx' : h + b = x := hbx
    have := hAC a ha
    have := hAC b hb
    omega
  have hVcard : 2 * A.card ≤ V.card := by
    rw [hV, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj1,
      Finset.card_image_of_injOn hinj2]
    omega
  have hVmem : ∀ x ∈ V, (∃ a ∈ A, x = h - a) ∨ (∃ a ∈ A, x = h + a) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
      exact Or.inl ⟨a, ha, hax.symm⟩
    · obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
      exact Or.inr ⟨a, ha, hax.symm⟩
  have hV2h : ∀ x ∈ V, x ≤ 2 * h := by
    intro x hx
    rcases hVmem x hx with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · omega
    · have := hAC a ha
      omega
  -- no difference of two points is in `C i`
  have hnoti : ∀ x ∈ V, ∀ y ∈ V, x < y → y - x ∉ C i := by
    intro x hx y hy hxy hyx
    rcases hVmem x hx with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
      rcases hVmem y hy with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
    · obtain ⟨-, ha2, haC⟩ := hAC a ha
      obtain ⟨-, hb2, hbC⟩ := hAC b hb
      have e : h - b - (h - a) + b = a := by omega
      exact hC i _ hyx _ hbC (by rw [e]; exact haC)
    · obtain ⟨-, ha2, haC⟩ := hAC a ha
      obtain ⟨-, -, hbC⟩ := hAC b hb
      have e : h + b - (h - a) = a + b := by omega
      exact hC i a haC b hbC (by rw [← e]; exact hyx)
    · omega
    · obtain ⟨-, -, haC⟩ := hAC a ha
      obtain ⟨-, -, hbC⟩ := hAC b hb
      have e : h + b - (h + a) + a = b := by omega
      exact hC i _ hyx _ haC (by rw [e]; exact hbC)
  -- colour the pairs of `V` by the cover set of the difference
  set K := (Finset.univ.image fun j : Fin (k + 1) => (j : ℕ)).erase (i : ℕ) with hK
  have hKcard : K.card ≤ k := by
    have h1 : (Finset.univ.image fun j : Fin (k + 1) => (j : ℕ)).card ≤ k + 1 :=
      Finset.card_image_le.trans (by simp)
    have h2 : (i : ℕ) ∈ Finset.univ.image fun j : Fin (k + 1) => (j : ℕ) :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [hK, Finset.card_erase_of_mem h2]
    omega
  have hcolK : ∀ x ∈ V, ∀ y ∈ V, x < y → (f (y - x) : ℕ) ∈ K := by
    intro x hx y hy hxy
    rw [hK, Finset.mem_erase]
    refine ⟨fun heq => ?_, Finset.mem_image.mpr ⟨f (y - x), Finset.mem_univ _, rfl⟩⟩
    have hfi : f (y - x) = i := Fin.ext heq
    have hy2 := hV2h y hy
    have hmemf := hf (y - x) (by omega) (by omega)
    rw [hfi] at hmemf
    exact hnoti x hx y hy hxy hmemf
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, h1, h2⟩ :=
    hR V K (fun x y => (f (y - x) : ℕ)) hKcard (by omega) hcolK
  -- a monochromatic triangle is a Schur triple in one cover set
  have e1 : f (y - x) = f (z - y) := Fin.ext h1
  have e2 : f (y - x) = f (z - x) := Fin.ext h2
  have hz2 := hV2h z hz
  have m1 := hf (y - x) (by omega) (by omega)
  have m2 := hf (z - y) (by omega) (by omega)
  have m3 := hf (z - x) (by omega) (by omega)
  rw [← e1] at m2
  rw [← e2] at m3
  exact hC (f (y - x)) _ m1 _ m2 (by rw [show y - x + (z - y) = z - x by omega]; exact m3)

/-- `S(3) ≤ 13`: the centred bound with `R_2(3) ≤ 6`. The bound is exact,
since `S(3) = 13`. -/
theorem not_coveredBySumFree_Icc_fourteen_three : ¬ CoveredBySumFree (Set.Icc 1 14) 3 := by
  have h6 : TriangleRamsey 2 6 := by
    have := triangleRamsey_ramseyBound 2
    rwa [show ramseyBound 2 = 6 by decide] at this
  exact not_coveredBySumFree_Icc_of_triangleRamsey h6

/-- `R_4(3) ≤ 61` implies `S(6) ≤ 1801`: then `R_5(3) ≤ 302`, and the
centred bound gives that `[1, 1802]` is not covered by six sumfree sets.
`R_4(3) ≤ 61` is a hypothesis here (see the module docstring). -/
theorem not_coveredBySumFree_Icc_six_of_triangleRamsey_four_sixtyOne
    (h : TriangleRamsey 4 61) : ¬ CoveredBySumFree (Set.Icc 1 1802) 6 :=
  not_coveredBySumFree_Icc_of_triangleRamsey (k := 5) (r := 302) (triangleRamsey_succ h)

end ClassicalSchur

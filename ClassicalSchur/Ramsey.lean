/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import ClassicalSchur.Basic

/-!
# Monochromatic triangles

`TriangleRamsey k N` says: every colouring, with at most `k` colours, of the
pairs `x < y` of a set of at least `N` naturals has a monochromatic triangle.
In the usual notation this is `R_k(3) ≤ N`. `ramseyBound` is the pigeonhole
recursion `R_{k+1}(3) ≤ (k+1)(R_k(3) − 1) + 2` from `R_0(3) = 2`, so
`ramseyBound 2 = 6`, `ramseyBound 3 = 17` and `ramseyBound 4 = 66`, and
`TriangleRamsey k (ramseyBound k)` holds for every `k`.
-/

@[expose] public section

namespace ClassicalSchur


/-- Every colouring with at most `k` colours of the pairs `x < y` of a set
of at least `N` naturals has a monochromatic triangle. -/
def TriangleRamsey (k N : ℕ) : Prop :=
  ∀ (V K : Finset ℕ) (c : ℕ → ℕ → ℕ), K.card ≤ k → N ≤ V.card →
    (∀ x ∈ V, ∀ y ∈ V, x < y → c x y ∈ K) →
    ∃ x ∈ V, ∃ y ∈ V, ∃ z ∈ V, x < y ∧ y < z ∧ c x y = c y z ∧ c x y = c x z

/-- The pigeonhole upper bound for the triangle Ramsey numbers:
`2, 3, 6, 17, 66, …`. -/
def ramseyBound : ℕ → ℕ
  | 0 => 2
  | k + 1 => (k + 1) * (ramseyBound k - 1) + 2

theorem two_le_ramseyBound (k : ℕ) : 2 ≤ ramseyBound k := by
  cases k <;> simp [ramseyBound]

theorem ramseyBound_three : ramseyBound 3 = 17 := by decide

theorem ramseyBound_four : ramseyBound 4 = 66 := by decide

/-- The pigeonhole bound: `k` colours force a monochromatic triangle on
`ramseyBound k` vertices. -/
theorem triangleRamsey_ramseyBound (k : ℕ) : TriangleRamsey k (ramseyBound k) := by
  induction k with
  | zero =>
    intro V K c hK hV hc
    have hK0 : K = ∅ := Finset.card_eq_zero.mp (by omega)
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < V.card by simp [ramseyBound] at hV; omega)
    rcases lt_or_gt_of_ne hab with h | h
    · simpa [hK0] using hc a ha b hb h
    · simpa [hK0] using hc b hb a ha h
  | succ k ih =>
    intro V K c hK hV hc
    have h2 := two_le_ramseyBound (k + 1)
    have hVne : V.Nonempty := by rw [← Finset.card_pos]; omega
    set v := V.min' hVne with hv
    have hvV : v ∈ V := V.min'_mem hVne
    set W := V.erase v with hW
    have hWcard : (k + 1) * (ramseyBound k - 1) + 1 ≤ W.card := by
      rw [hW, Finset.card_erase_of_mem hvV]
      simp only [ramseyBound] at hV
      omega
    have hvW : ∀ w ∈ W, v < w := fun w hw =>
      lt_of_le_of_ne (V.min'_le w (Finset.mem_of_mem_erase hw)) (Finset.ne_of_mem_erase hw).symm
    have hmaps : ∀ w ∈ W, c v w ∈ K := fun w hw =>
      hc v hvV w (Finset.mem_of_mem_erase hw) (hvW w hw)
    have hlt : K.card * (ramseyBound k - 1) < W.card :=
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
      obtain ⟨x, hx, y, hy, z, hz, h1, h2, h3, h4⟩ := ih U (K.erase i) c
        (by rw [Finset.card_erase_of_mem hiK]; omega) (by omega)
        (fun x hx y hy hxy =>
          Finset.mem_erase.mpr ⟨hmono x hx y hy hxy, hc x (hUV hx) y (hUV hy) hxy⟩)
      exact ⟨x, hUV hx, y, hUV hy, z, hUV hz, h1, h2, h3, h4⟩

end ClassicalSchur

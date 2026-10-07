/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_le_of_exceptional_set {X : Type*} [Fintype X] [Nonempty X]
    (E : Finset X) (F : X → ℝ) {A B delta : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hE : (E.card : ℝ) ≤ delta * Fintype.card X)
    (hbound : ∀ x, F x ≤ B) (hgood : ∀ x, x ∉ E → F x ≤ A) :
    (𝔼 x, F x) ≤ A + B * delta := by
  classical
  have hcard : (0 : ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have hind : (𝔼 x : X, if x ∈ E then (1 : ℝ) else 0) ≤ delta := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact (div_le_iff₀ hcard).mpr hE
  calc
    _ ≤ 𝔼 x, (A + B * (if x ∈ E then (1 : ℝ) else 0)) := by
      apply Finset.expect_le_expect
      intro x _
      by_cases hx : x ∈ E
      · simpa only [ite_eq_left hx, mul_one] using (hbound x).trans (le_add_of_nonneg_left hA)
      · simpa only [ite_eq_right hx, mul_zero, add_zero] using hgood x hx
    _ = A + B * (𝔼 x : X, if x ∈ E then (1 : ℝ) else 0) := by
      rw [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hind hB)

end Erdos3

end

end OAI

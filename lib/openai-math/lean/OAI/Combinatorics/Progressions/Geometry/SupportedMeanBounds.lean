import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_expect_le_of_nonneg_bound {X : Type*} (s : Finset X) (f : X → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x ∈ s, f x ≤ C) : (𝔼 x ∈ s, f x) ≤ C := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hC
  · exact (Finset.expect_le_expect hf).trans_eq (Finset.expect_const hs C)

theorem finiteMean_le_of_support {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (f : X → ℝ) {C : ℝ}
    (hf : ∀ x, p.weight x ≠ 0 → f x ≤ C) : p.mean f ≤ C := by
  rw [← p.mean_const C]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p.weight x = 0
  · simp only [hx, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left (hf x hx) (p.nonneg x)

end Erdos3

end

end OAI

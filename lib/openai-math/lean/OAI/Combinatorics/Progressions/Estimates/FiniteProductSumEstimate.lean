import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_expect_product_sum_le {I J X : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype X]
    (c : I → J → ℂ) (A : I → J → X → ℂ) {error : ℝ}
    (hc : ∀ i j, ‖c i j‖ = 1)
    (hA : ∀ choice : I → J, ‖𝔼 x, ∏ i, A i (choice i) x‖ ≤ error) :
    ‖𝔼 x, ∏ i, ∑ j, c i j * A i j x‖ ≤ (Fintype.card J : ℝ) ^ Fintype.card I * error := by
  have he : (𝔼 x, ∏ i, ∑ j, c i j * A i j x) =
      ∑ choice : I → J, (∏ i, c i (choice i)) * (𝔼 x, ∏ i, A i (choice i) x) := by
    simp only [Fintype.prod_sum, Finset.prod_mul_distrib, Finset.expect_sum_comm, ← Finset.mul_expect]
  rw [he]
  calc
    _ ≤ ∑ choice : I → J, ‖(∏ i, c i (choice i)) * (𝔼 x, ∏ i, A i (choice i) x)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _choice : I → J, error := by
      apply Finset.sum_le_sum
      intro choice _
      simpa only [norm_mul, norm_prod, hc, Finset.prod_const_one, one_mul] using hA choice
    _ = _ := by simp

end Erdos3

end

end OAI

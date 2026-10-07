import OAI.Combinatorics.Progressions.Estimates.RelativeFiberSlicePatch

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

theorem finiteProductIntegral_const (w : I → X → ℝ) (c : ℝ) :
    finiteProductIntegral w (fun _ => c) = (∏ i, ∑ x, w i x) * c := by
  unfold finiteProductIntegral
  rw [← Finset.sum_mul]
  exact congrArg (fun t : ℝ => t * c) (Fintype.prod_sum w).symm

theorem finiteProductIntegral_const_of_mass_one (w : I → X → ℝ)
    (hw : ∀ i, ∑ x, w i x = 1) (c : ℝ) :
    finiteProductIntegral w (fun _ => c) = c := by
  rw [finiteProductIntegral_const]
  simp only [hw, Finset.prod_const_one, one_mul]

end Erdos3

end

end OAI

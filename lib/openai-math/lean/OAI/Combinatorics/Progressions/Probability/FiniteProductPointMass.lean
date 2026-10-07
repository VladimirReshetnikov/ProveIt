import OAI.Combinatorics.Progressions.Estimates.FiniteSectionPermutation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

theorem finiteProductIntegral_pointMass (w : I → X → ℝ) (z : I → X) (f : (I → X) → ℝ) :
    finiteProductIntegral (fun i => finiteSectionWeight (w i) true (z i)) f = f z := by
  classical
  unfold finiteProductIntegral
  rw [Finset.sum_eq_single z]
  · simp [finiteSectionWeight]
  · intro v _ hv
    have hne : ∃ i, v i ≠ z i := by
      by_contra h
      push Not at h
      exact hv (funext h)
    obtain ⟨i, hi⟩ := hne
    have hz : finiteSectionWeight (w i) true (z i) (v i) = 0 := by
      simp only [finiteSectionWeight, ite_true, hi, ite_false]
    have hp : (∏ j, finiteSectionWeight (w j) true (z j) (v j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [hp, zero_mul]
  · simp

end Erdos3

end

end OAI

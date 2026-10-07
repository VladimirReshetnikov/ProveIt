import OAI.Combinatorics.Progressions.Estimates.FiniteSectionPermutation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteSectionIntegral_eq_zero_of_fixed (w : ℕ → X → ℝ) (n : ℕ)
    (s : Fin n → Bool) (f : (Fin n → X) → ℝ) (z : Fin n → X)
    (j : Fin n) (hj : s j = true) (hf : ∀ v, v j = z j → f v = 0) :
    finiteSectionIntegral w n s f z = 0 := by
  classical
  rw [finiteSectionIntegral_eq_product]
  unfold finiteProductIntegral
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v j = z j
  · rw [hf v hv, mul_zero]
  · have hz : finiteSectionWeight (w j) (s j) (z j) (v j) = 0 := by
      simp only [finiteSectionWeight, hj, ite_true, hv, ite_false]
    have hp : (∏ i : Fin n, finiteSectionWeight (w i) (s i) (z i) (v i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hz
    rw [hp, zero_mul]

theorem finiteSectionL2Norm_eq_zero_of_fixed (w : ℕ → X → ℝ) (n : ℕ)
    (s : Fin n → Bool) (f : (Fin n → X) → ℝ) (z : Fin n → X)
    (j : Fin n) (hj : s j = true) (hf : ∀ v, v j = z j → f v = 0) :
    finiteSectionL2Norm w n s f z = 0 := by
  unfold finiteSectionL2Norm
  rw [finiteSectionIntegral_eq_zero_of_fixed w n s _ z j hj
    (fun v hv => by rw [hf v hv]; norm_num), Real.sqrt_zero]

end Erdos3

end

end OAI

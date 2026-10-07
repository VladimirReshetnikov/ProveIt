import OAI.Combinatorics.Progressions.Probability.CoefficientJetDensityFactors

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {O J : Type*} [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]

omit [Fintype O] [DecidableEq O] [DecidableEq J] in
theorem integerMatrixImagePMF_preimage_of_toReal_ne_zero
    (A : Matrix O J ℤ) (p : J → PMF ℤ) (y : O → ℤ)
    (hy : (integerMatrixImagePMF A p y).toReal ≠ 0) :
    ∃ z : J → ℤ, (∀ j, z j ∈ (p j).support) ∧ A *ᵥ z = y := by
  have hy' : y ∈ (integerMatrixImagePMF A p).support := by
    apply (PMF.mem_support_iff _ _).mpr
    intro h
    exact hy (by rw [h, ENNReal.toReal_zero])
  obtain ⟨z, hz, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hy'
  refine ⟨z, ?_, heq⟩
  intro j
  apply (PMF.mem_support_iff _ _).mpr
  intro h
  apply (PMF.mem_support_iff _ _).mp hz
  rw [independentProductPMF_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) h

omit [Fintype O] [DecidableEq O] [DecidableEq J] in
theorem integerMatrixImagePMF_scaled_support_bound
    (A : Matrix O J ℤ) (p : J → PMF ℤ) (T : J → ℝ) (hT : ∀ j, 0 < T j)
    {H M R : ℝ} (hM : 0 ≤ M)
    (hA : ∀ o j, |(A o j : ℝ)| / T j ≤ M)
    (hp : ∀ j z, z ∈ (p j).support → |(z : ℝ) / H| * T j ≤ R)
    (y : O → ℤ) (hy : (integerMatrixImagePMF A p y).toReal ≠ 0) (o : O) :
    |(y o : ℝ) / H| ≤ (Fintype.card J : ℝ) * M * R := by
  obtain ⟨z, hz, rfl⟩ := integerMatrixImagePMF_preimage_of_toReal_ne_zero A p y hy
  calc
    _ = |∑ j, (A o j : ℝ) * ((z j : ℝ) / H)| := by
      simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_div, mul_div_assoc]
    _ ≤ ∑ j, |(A o j : ℝ) * ((z j : ℝ) / H)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : J, M * R := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      calc
        _ ≤ (M * T j) * |(z j : ℝ) / H| :=
          mul_le_mul_of_nonneg_right ((div_le_iff₀ (hT j)).mp (hA o j)) (abs_nonneg _)
        _ = M * (|(z j : ℝ) / H| * T j) := by ring
        _ ≤ M * R := mul_le_mul_of_nonneg_left (hp j (z j) (hz j)) hM
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

end Erdos3

end

end OAI

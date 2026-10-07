import OAI.Combinatorics.Progressions.Polynomial.PolynomialTranslationActionCompatibility

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*} {w : σ → ℕ}

theorem integerWeightedLowering_preimage (e : WeightedLoweringAut w ℚ)
    (he : ∀ i, e.val (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} {n : ℕ} (hP : P ∈ integerCoefficientPolynomials σ)
    (hdegree : P ∈ weightedSupportLE w n) :
    ∃ Q, Q ∈ integerCoefficientPolynomials σ ∧ Q ∈ weightedSupportLE w n ∧ e.val Q = P := by
  induction n generalizing P with
  | zero =>
    refine ⟨P, hP, hdegree, ?_⟩
    exact sub_eq_zero.mp (weightedSupportLT_zero_eq (e.difference_lower hdegree))
  | succ n ih =>
    have hI : e.val P - P ∈ integerCoefficientPolynomials σ :=
      (integerCoefficientPolynomials σ).sub_mem (integerPolynomialHom_preserves e.val.toAlgHom he hP) hP
    have hD : e.val P - P ∈ weightedSupportLE w n :=
      weightedSupportLT_succ_le (e.difference_lower hdegree)
    obtain ⟨Q, hQI, hQD, hQ⟩ := ih hI hD
    refine ⟨P - Q, (integerCoefficientPolynomials σ).sub_mem hP hQI,
      (weightedSupportLE w (n + 1)).sub_mem hdegree (weightedSupportLE_mono (Nat.le_succ n) hQD), ?_⟩
    rw [map_sub, hQ]
    abel

theorem integerWeightedLowering_inverse_preserves (e : WeightedLoweringAut w ℚ)
    (he : ∀ i, e.val (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    e.val.symm P ∈ integerCoefficientPolynomials σ := by
  obtain ⟨Q, hQI, _, hQ⟩ := integerWeightedLowering_preimage e he hP
    ((mem_weightedSupportLE_iff w _ P).mpr le_rfl)
  have hEQ : e.val.symm P = Q := by
    apply e.val.injective
    rw [e.val.apply_symm_apply, hQ]
  rw [hEQ]
  exact hQI

noncomputable def integerWeightedLoweringSubgroup (w : σ → ℕ) : Subgroup (WeightedLoweringAut w ℚ) where
  carrier := {e | ∀ i, e.val (X i) ∈ integerCoefficientPolynomials σ}
  one_mem' := fun i => integerCoefficientPolynomials_X i
  mul_mem' := by
    intro e f he hf i
    exact integerPolynomialHom_preserves e.val.toAlgHom he (hf i)
  inv_mem' := by
    intro e he i
    exact integerWeightedLowering_inverse_preserves e he (integerCoefficientPolynomials_X i)

theorem integerWeightedLowering_preserves (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    e.val P ∈ integerCoefficientPolynomials σ :=
  integerPolynomialHom_preserves e.val.toAlgHom he hP

theorem integerWeightedLowering_difference_pow (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) (k : ℕ) :
    (polynomialHomDifference e.val.toAlgHom ^ k) P ∈ integerCoefficientPolynomials σ := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (integerCoefficientPolynomials σ).sub_mem (integerWeightedLowering_preserves e he ih) ih

end Erdos3

end

end OAI

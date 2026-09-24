import Surreal.Foundations.OmnificFloor

/-!
# Truncation of a positive and a negative monomial

Support calculations for the full-surreal contrast following `odg:ex:pell2`.
They use the actual canonical normal form and its strictly positive truncation.
-/

universe u
namespace Surreal.Foundations.SignSequence

open SmallNormalForm

noncomputable section

/-- A two-term expression with opposite nonzero growth exponents has the stated negative coefficient. -/
theorem twoTerm_negative_coeff (a : SignSequence.{u}) (ha : 0 < a) (A B : ℝ) :
    coeff (normalForm (ofReal A * omegaPower a + ofReal B * omegaPower (-a))) (-a) = B := by
  have hne : -a ≠ a := ne_of_lt (by linarith)
  rw [normalForm_add, normalForm_real_mul_omegaPower, normalForm_real_mul_omegaPower]
  simp [hne]

/-- A nonzero negative coefficient excludes membership in the real nonnegative-support ring. -/
theorem twoTerm_not_mem_nonnegativeSupport (a : SignSequence.{u}) (ha : 0 < a)
    (A B : ℝ) (hB : B ≠ 0) :
    ofReal A * omegaPower a + ofReal B * omegaPower (-a) ∉ nonnegativeSupportSubring := by
  intro h
  have hc := (mem_nonnegativeSupportSubring_iff _).mp h (-a) (neg_neg_of_pos ha)
  rw [twoTerm_negative_coeff a ha] at hc
  exact hB hc

/-- The canonical positive-growth truncation removes exactly the negative-exponent monomial. -/
theorem twoTerm_positiveGrowthPart (a : SignSequence.{u}) (ha : 0 < a) (A B : ℝ) :
    omnificToSurreal (positiveGrowthPart
      (ofReal A * omegaPower a + ofReal B * omegaPower (-a))) = ofReal A * omegaPower a := by
  change cutEvaluation (trunc (normalForm _) 0) = _
  rw [normalForm_add, normalForm_real_mul_omegaPower, normalForm_real_mul_omegaPower,
    ← cutEvaluation_single]
  congr 1
  apply SmallNormalForm.ext
  intro b
  by_cases hba : b = a
  · subst b
    have hne : a ≠ -a := ne_of_gt (by linarith)
    simp [coeff_trunc, coeff_add, coeff_single, ha, hne]
  · by_cases hbn : b = -a
    · subst b
      have hna : -a ≠ a := ne_of_lt (by linarith)
      simp [coeff_trunc, coeff_single, not_lt.mpr (neg_nonpos.mpr ha.le), hna]
    · simp [coeff_trunc, coeff_add, coeff_single, hba, hbn]

end
end Surreal.Foundations.SignSequence

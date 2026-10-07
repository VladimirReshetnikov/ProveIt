import GowersSzemeredi.Proofs13FourierSquareExtraction

/-! Comparing the retained extraction exponent with the printed target.
These inequalities compare estimates; they do not refute Theorem 13.12. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Substituting the Fourier density lower bound into the Section 13 spectral
parameter already exceeds the outer exponent in the printed target. -/
theorem section13_fourier_spectral_lower {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (1 / alpha) ^ ((2 : Nat) ^ 70) ≤
      section13Q ((alpha / 2) ^ ((2 : Nat) ^ 66)) := by
  have ha : 0 < alpha / 2 := by positivity
  have hhalf : alpha / 2 ≤ alpha := by linarith only [hα]
  have hcollapse : ((alpha / 2) ^ ((2 : Nat) ^ 66)) ^ (-((2 : Real) ^ 21)) =
      (alpha / 2) ^ (-((2 : Real) ^ 87)) := by
    rw [← Real.rpow_natCast (alpha / 2) ((2 : Nat) ^ 66), ← Real.rpow_mul ha.le]
    congr 1
    norm_num
  have hbase : (1 / alpha) ^ ((2 : Nat) ^ 70) = alpha ^ (-((2 : Real) ^ 70)) := by
    rw [Real.rpow_neg_eq_inv_rpow]
    rw [show (2 : Real) ^ 70 = (((2 : Nat) ^ 70 : Nat) : Real) by norm_cast,
      Real.rpow_natCast]
    simp only [one_div]
  calc
    _ = alpha ^ (-((2 : Real) ^ 70)) := hbase
    _ ≤ alpha ^ (-((2 : Real) ^ 87)) :=
      Real.rpow_le_rpow_of_exponent_ge hα hαone (by norm_num)
    _ ≤ (alpha / 2) ^ (-((2 : Real) ^ 87)) :=
      Real.rpow_le_rpow_of_nonpos ha hhalf (by norm_num)
    _ = ((alpha / 2) ^ ((2 : Nat) ^ 66)) ^ (-((2 : Real) ^ 21)) := hcollapse.symm
    _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg (pow_nonneg ha.le _) _)
      (one_le_pow₀ (by norm_num))

/-- The exponent proved by the complete extraction is strictly smaller than
the printed Theorem 13.12 exponent at every admissible alpha. Thus the printed
length cannot be obtained merely by weakening this particular lower bound;
a sharper construction or an independently justified repair is required. -/
theorem section13_extraction_exponent_lt_printed {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    section13SquareExponent ((alpha / 2) ^ ((2 : Nat) ^ 66)) <
      (1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70)) := by
  let delta := (alpha / 2) ^ ((2 : Nat) ^ 66)
  let x := (1 / alpha) ^ ((2 : Nat) ^ 70)
  have hδ : 0 < delta := pow_pos (by positivity) _
  have hδone : delta ≤ 1 := pow_le_one₀ (by positivity) (by linarith only [hαone])
  have hQ : 0 < section13Q delta := by unfold section13Q; positivity
  have hxQ : x ≤ section13Q delta := section13_fourier_spectral_lower hα hαone
  have hstrict : x < 13 * section13Q delta := by linarith only [hxQ, hQ]
  have hpref : (2 : Real) ^ (-(386 : Int)) * delta ^ 1856 ≤ 1 :=
    mul_le_one₀ (zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num))
      (pow_nonneg hδ.le _) (pow_le_one₀ hδ.le hδone)
  rw [section13SquareExponent_formula]
  calc
    _ ≤ 1 / (2 : Real) ^ (13 * section13Q delta) :=
      div_le_div_of_nonneg_right hpref (Real.rpow_nonneg (by norm_num) _)
    _ < 1 / (2 : Real) ^ x := one_div_lt_one_div_of_lt
      (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hstrict)
    _ = _ := by rw [one_div, one_div, Real.inv_rpow (by norm_num)]

end LeanProofs.GowersSzemeredi

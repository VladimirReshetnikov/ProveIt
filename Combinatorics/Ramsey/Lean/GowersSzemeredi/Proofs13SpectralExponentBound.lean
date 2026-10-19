import GowersSzemeredi.Proofs13CompleteSquareExtraction

/-! Elementary exponential estimates for the retained square exponent. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A simple exponential majorant, used to absorb polynomial prefactors. -/
theorem le_two_rpow_two_mul {x : Real} (hx : 0 ≤ x) : x ≤ (2 : Real) ^ (2 * x) := by
  have hlog : (1 : Real) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have hlin := Real.add_one_le_exp (Real.log 2 * (2 * x))
  rw [Real.rpow_def_of_pos (by norm_num)]
  nlinarith only [hlog, hlin, hx]

/-- The enormous spectral parameter absorbs the polynomial and fixed
prefactors in the checked square exponent. -/
theorem section13SquareExponent_ge_spectral_power {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    (2 : Real) ^ (-(15 * section13Q delta)) ≤ section13SquareExponent delta := by
  let Q := section13Q delta
  have hQinv : 3712 * delta⁻¹ ≤ Q := mul_le_mul
    ((by norm_num : (3712 : Real) ≤ 2 ^ 12).trans (pow_le_pow_right₀ one_le_two (by norm_num)))
    ((Real.rpow_neg_one delta).symm.trans_le
      (Real.rpow_le_rpow_of_exponent_ge hδ hδone (by norm_num)))
    (inv_nonneg.mpr hδ.le) (by positivity)
  have hδpow : (2 : Real) ^ (-Q) ≤ delta ^ 1856 := by
    rw [Real.rpow_neg zero_le_two, inv_le_comm₀ (by positivity) (pow_pos hδ _), ← inv_pow]
    calc delta⁻¹ ^ 1856 ≤ ((2 : Real) ^ (2 * delta⁻¹)) ^ 1856 :=
          pow_le_pow_left₀ (inv_nonneg.2 hδ.le) (le_two_rpow_two_mul (inv_nonneg.2 hδ.le)) _
      _ = (2 : Real) ^ (3712 * delta⁻¹) := by
          rw [← Real.rpow_mul_natCast zero_le_two]
          congr 1
          ring
      _ ≤ (2 : Real) ^ Q := Real.rpow_le_rpow_of_exponent_le one_le_two hQinv
  have hconst : (2 : Real) ^ (-Q) ≤ (2 : Real) ^ (-(386 : Int)) :=
    (Real.rpow_le_rpow_of_exponent_le one_le_two
      (by push_cast; linarith only [hQinv, (one_le_inv₀ hδ).mpr hδone])).trans_eq
      (Real.rpow_intCast 2 _)
  rw [section13SquareExponent_formula]
  calc
    _ = ((2 : Real) ^ (-Q) * (2 : Real) ^ (-Q)) / (2 : Real) ^ (13 * Q) := by
      rw [← Real.rpow_add two_pos, ← Real.rpow_sub two_pos]
      congr 1
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul hconst hδpow (by positivity) (by positivity)) (by positivity)

end LeanProofs.GowersSzemeredi

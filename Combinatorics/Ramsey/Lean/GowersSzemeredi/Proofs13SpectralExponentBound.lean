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
  have hC : (3712 : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 20) := by
    calc
      _ ≤ (2 : Real) ^ (12 : Nat) := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hpower : delta⁻¹ ≤ delta ^ (-((2 : Real) ^ 21)) := by
    calc
      _ = delta ^ (-(1 : Real)) := (Real.rpow_neg_one delta).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδone (by norm_num)
  have hQinv : 3712 * delta⁻¹ ≤ Q :=
    mul_le_mul hC hpower (inv_nonneg.mpr hδ.le) (by positivity)
  have hinv : 1 ≤ delta⁻¹ := (one_le_inv₀ hδ).mpr hδone
  have hQ386 : 386 ≤ Q := by nlinarith only [hQinv, hinv]
  have hδpow : delta ^ 1856 ≥ (2 : Real) ^ (-Q) := by
    have hgrow := pow_le_pow_left₀ (inv_nonneg.mpr hδ.le)
      (le_two_rpow_two_mul (inv_nonneg.mpr hδ.le)) 1856
    have hexp : ((2 : Real) ^ (2 * delta⁻¹)) ^ 1856 = (2 : Real) ^ (3712 * delta⁻¹) := by
      rw [← Real.rpow_mul_natCast (by norm_num)]
      congr 1
      ring
    rw [hexp] at hgrow
    have hupper : (delta ^ 1856)⁻¹ ≤ (2 : Real) ^ Q := by
      simpa only [inv_pow] using hgrow.trans
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hQinv)
    have hi := inv_anti₀ (inv_pos.mpr (pow_pos hδ 1856)) hupper
    simpa only [inv_inv, Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)] using hi
  have hconst : (2 : Real) ^ (-Q) ≤ (2 : Real) ^ (-(386 : Int)) := by
    rw [← Real.rpow_intCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith only [hQ386]
  rw [section13SquareExponent_formula]
  calc
    _ = ((2 : Real) ^ (-Q) * (2 : Real) ^ (-Q)) / (2 : Real) ^ (13 * Q) := by
      rw [← Real.rpow_add (by norm_num), ← Real.rpow_sub (by norm_num)]
      congr 1
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul hconst hδpow (Real.rpow_nonneg (by norm_num) _) (by positivity))
      (Real.rpow_nonneg (by norm_num) _)

end LeanProofs.GowersSzemeredi

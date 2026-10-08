import GowersSzemeredi.Proofs16CubicAllScaleCover

/-! A rational lower bound for the all-scale exponent cap. Taking logarithms
of the explicit rounding threshold cancels its inverse powers. The bound
retains a constant multiple of the product of the two lifting exponents. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem log_positivePowerThreshold {C D e : Real}
    (hD : 0 < D) (he : 0 < e) (hCD : D ≤ C) :
    Real.log (positivePowerThreshold C D e) = Real.log (C / D) / e := by
  have hratio : 1 ≤ C / D := (one_le_div hD).mpr hCD
  rw [positivePowerThreshold, max_eq_right hratio,
    max_eq_right (Real.one_le_rpow hratio (inv_nonneg.mpr he.le)),
    Real.log_rpow (lt_of_lt_of_le zero_lt_one hratio)]
  ring

/-- The logarithm of the rounded lifting threshold has only reciprocal
linear dependence on the product of the two exponents. -/
theorem section16_log_rounded_threshold_le {z e a : Real}
    (hz : 0 < z) (hz1 : z ≤ 1) (he : 0 < e) (ha : 0 < a) (ha1 : a ≤ 1) :
    Real.log (section16RoundedPowerThreshold z e a) ≤
      (8 + 2 * Real.log (16 / z)) / (e * a) := by
  have hL : 0 ≤ Real.log (16 / z) :=
    Real.log_nonneg ((one_le_div hz).mpr (by linarith))
  have hp : 0 < (z / 16) ^ (a / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hp1 : (z / 16) ^ (a / 2) ≤ 1 :=
    Real.rpow_le_one (by positivity) (by linarith) (by positivity)
  have hD : 0 < (z / 16) ^ (a / 2) / 4 := by positivity
  have hlog : Real.log (1 / ((z / 16) ^ (a / 2) / 4)) =
      Real.log 4 + a / 2 * Real.log (16 / z) := by
    rw [Real.log_div one_ne_zero hD.ne', Real.log_one,
      Real.log_div hp.ne' (by norm_num), Real.log_rpow (by positivity)]
    rw [Real.log_div hz.ne' (by norm_num), Real.log_div (by norm_num) hz.ne']
    ring
  have hlog4 : Real.log 4 ≤ 2 := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
      linarith
    have hh : Real.log (4 : Real) = 2 * Real.log 2 := by
      rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num, Real.log_pow]
      norm_num
    linarith
  have hfirst : Real.log (positivePowerThreshold 16 z e) ≤
      (8 + 2 * Real.log (16 / z)) / (e * a) := by
    rw [log_positivePowerThreshold hz he (by linarith)]
    apply (le_div_iff₀ (mul_pos he ha)).mpr
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right ha1 hL]
  have hsecond : Real.log (positivePowerThreshold 1 ((z / 16) ^ (a / 2) / 4)
      (e * a / 4)) ≤ (8 + 2 * Real.log (16 / z)) / (e * a) := by
    rw [log_positivePowerThreshold hD (by positivity) (by linarith), hlog]
    apply (div_le_div_iff₀ (by positivity : 0 < e * a / 4) (mul_pos he ha)).mpr
    have hh := mul_le_mul_of_nonneg_right ha1 hL
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog4) (mul_pos he ha).le,
      mul_nonneg (sub_nonneg.mpr hh) (mul_pos he ha).le]
  unfold section16RoundedPowerThreshold section16RoundedExponentThreshold
  rw [show e * a / 2 - e * a / 4 = e * a / 4 by ring]
  rcases le_total (positivePowerThreshold 16 z e)
    (positivePowerThreshold 1 ((z / 16) ^ (a / 2) / 4) (e * a / 4)) with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

/-- Capping the large-box exponent to cover short boxes still leaves an
explicit constant multiple of the product of the line and slice exponents. -/
theorem section16_cubic_capped_exponent_lower {z e a : Real}
    (hz : 0 < z) (hz1 : z ≤ 1) (he : 0 < e) (he1 : e ≤ 1)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    e * a / (16 + 4 * Real.log (16 / z)) ≤
      section16CappedWidthExponent (e * a / 4) (section16RoundedPowerThreshold z e a) := by
  have hL : 0 ≤ Real.log (16 / z) :=
    Real.log_nonneg ((one_le_div hz).mpr (by linarith))
  have hD : 0 < 16 + 4 * Real.log (16 / z) := by positivity
  have hlog2 : (1 / 2 : Real) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at hh ⊢
    exact hh
  have hea : 0 < e * a := mul_pos he ha
  have hea1 : e * a ≤ 1 := (mul_le_of_le_one_right he.le ha1).trans he1
  have hT : 0 < Real.log (max 2 (section16RoundedPowerThreshold z e a)) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hlogT : Real.log (max 2 (section16RoundedPowerThreshold z e a)) ≤
      (8 + 2 * Real.log (16 / z)) / (e * a) := by
    rcases le_total (2 : Real) (section16RoundedPowerThreshold z e a) with h | h
    · rw [max_eq_right h]
      exact section16_log_rounded_threshold_le hz hz1 he ha ha1
    · rw [max_eq_left h]
      have hh : Real.log (2 : Real) ≤ 1 := by
        have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
        linarith
      apply hh.trans
      apply (le_div_iff₀ hea).mpr
      nlinarith
  apply le_min
  · exact div_le_div_of_nonneg_left hea.le (by norm_num) (by linarith)
  · apply (le_div_iff₀ hT).mpr
    have hh := mul_le_mul_of_nonneg_left hlogT (div_nonneg hea.le hD.le)
    have heq : e * a / (16 + 4 * Real.log (16 / z)) *
        ((8 + 2 * Real.log (16 / z)) / (e * a)) = (1 / 2 : Real) := by
      field_simp
      ring
    rw [heq] at hh
    exact hh.trans hlog2

end LeanProofs.GowersSzemeredi

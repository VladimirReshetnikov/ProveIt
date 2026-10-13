import GowersSzemeredi.Proofs18FejerInverseThresholdEnvelope

/-! Numerical budgets for the gain, length coefficient, and iteration
base of the complete five-term argument. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem fejerCubicDiscrepancyParameter_le_one {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) : fejerCubicDiscrepancyParameter alpha ≤ 1 := by
  let a := fejerCubicLocalQuadraticParameter alpha
  have ha : 0 < a := fejerCubicLocalQuadraticParameter_pos hα
  have ha1 : a ≤ 1 := fejerCubicLocalQuadraticParameter_le_one hα.le hαone
  have hm : fejerCubicLocalizedMassParameter alpha ≤ 1 := by
    unfold fejerCubicLocalizedMassParameter
    have h1 : (2 : Real) ^ (-(59 : Int)) * alpha ^ 2 ≤ 1 :=
      (mul_le_mul (by norm_num : (2 : Real) ^ (-(59 : Int)) ≤ 1)
        (pow_le_one₀ hα.le hαone) (by positivity) zero_le_one).trans (by norm_num)
    exact (mul_le_mul h1 (pow_le_one₀ (by positivity) (by linarith only [hαone]))
      (by positivity) zero_le_one).trans (by norm_num)
  have hq : quadraticDiscrepancyParameter a ≤ 1 := by
    unfold quadraticDiscrepancyParameter
    have h1 : (2 : Real) ^ (-(20 : Int)) * a ^ 2 ≤ 1 :=
      (mul_le_mul (by norm_num : (2 : Real) ^ (-(20 : Int)) ≤ 1)
        (pow_le_one₀ ha.le ha1) (by positivity) zero_le_one).trans (by norm_num)
    exact (mul_le_mul h1 (pow_le_one₀ (by positivity) (by linarith only [ha1]))
      (by positivity) zero_le_one).trans (by norm_num)
  change fejerCubicLocalizedMassParameter alpha * quadraticDiscrepancyParameter a / 2 ≤ 1
  have hp := mul_le_mul hm hq (by unfold quadraticDiscrepancyParameter; positivity) zero_le_one
  linarith only [hp]

theorem fejer_cubic_gain_inv_le_power {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (fejerCubicDiscrepancyParameter alpha / 8)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 60) := by
  have hx : 2 ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have h8 : (8 : Real) ≤ (2 / alpha) ^ (3 : Nat) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hx 3
    norm_num at h
    exact h
  rw [inv_div, div_eq_mul_inv]
  calc
    _ ≤ (2 / alpha) ^ (3 : Nat) * (2 / alpha) ^ ((2 : Nat) ^ 59) :=
      mul_le_mul h8 (fejerCubicDiscrepancyParameter_inv_le_power hα hαone)
        (inv_nonneg.mpr (fejerCubicDiscrepancyParameter_pos hα).le) (by positivity)
    _ = (2 / alpha) ^ (3 + (2 : Nat) ^ 59) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith only [hx]) (by norm_num)

set_option exponentiation.threshold 2048 in
theorem fejer_cubic_interval_length_factor_inv_le_power {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (fejerCubicDiscrepancyParameter alpha /
      (8 * boundaryRefinementConstant (fejerCubicDiscrepancyParameter alpha / 64)))⁻¹ ≤
      (2 / alpha) ^ ((2 : Nat) ^ 1084) := by
  have hx : 2 ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hfixed : section5LocalRefinementConstant 1 1 ≤ (2 / alpha) ^ ((2 : Nat) ^ 1082) :=
    (section5_degree_le_three_refinement_constant_upper (by omega)).trans
      (pow_le_pow_left₀ (by norm_num) hx _)
  have h := (interval_length_factor_bounds_of_powers hx
    (fejerCubicDiscrepancyParameter_pos hα) (fejerCubicDiscrepancyParameter_le_one hα hαone)
    (fejerCubicDiscrepancyParameter_inv_le_power hα hαone) hfixed).2.2
  exact h.trans (pow_le_pow_right₀ (by linarith only [hx]) (by norm_num))

theorem fejer_cubic_interval_length_factor_le_one {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    fejerCubicDiscrepancyParameter alpha /
      (8 * boundaryRefinementConstant (fejerCubicDiscrepancyParameter alpha / 64)) ≤ 1 := by
  have hb := fejerCubicDiscrepancyParameter_le_one hα hαone
  have hC := section5LocalRefinementConstant_ge_four 1
    (4 * Real.pi * (fejerCubicDiscrepancyParameter alpha / 64))
  have hCp : 0 < boundaryRefinementConstant (fejerCubicDiscrepancyParameter alpha / 64) := section5LocalRefinementConstant_pos _ _
  apply (div_le_one (by positivity : 0 < 8 * boundaryRefinementConstant (fejerCubicDiscrepancyParameter alpha / 64))).mpr
  change 4 ≤ boundaryRefinementConstant (fejerCubicDiscrepancyParameter alpha / 64) at hC
  linarith only [hb, hC]

theorem fejer_cubic_iteration_base_le_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    2 * max 1 (fejerCubicDiscrepancyExponent alpha / 16)⁻¹ ≤
      Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 62)) := by
  let x := 2 / alpha
  let A := x ^ ((2 : Nat) ^ 61)
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hA : 32 ≤ A := by
    calc
      _ = (2 : Real) ^ (5 : Nat) := by norm_num
      _ ≤ x ^ (5 : Nat) := pow_le_pow_left₀ (by norm_num) hx _
      _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num : (5 : Nat) ≤ (2 : Nat) ^ 61)
  have hAe : A ≤ Real.exp A := by have h := Real.add_one_le_exp A; linarith only [h]
  have hρ : (fejerCubicDiscrepancyExponent alpha / 16)⁻¹ ≤ 16 * Real.exp A := by
    rw [inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (fejerCubicDiscrepancyExponent_inv_le_exp hα hαone) (by norm_num)
  have hmax : max 1 (fejerCubicDiscrepancyExponent alpha / 16)⁻¹ ≤ 16 * Real.exp A :=
    max_le (by linarith only [hA, hAe]) hρ
  calc
    _ ≤ 32 * Real.exp A := by have h := mul_le_mul_of_nonneg_left hmax (by norm_num : (0 : Real) ≤ 2); linarith only [h]
    _ ≤ Real.exp A * Real.exp A := mul_le_mul_of_nonneg_right (hA.trans hAe) (Real.exp_pos _).le
    _ = Real.exp (2 * A) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ x * x ^ ((2 : Nat) ^ 61) := mul_le_mul_of_nonneg_right hx (by positivity)
        _ = x ^ ((2 : Nat) ^ 61 + 1) := (pow_succ' _ _).symm
        _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num)

end LeanProofs.GowersSzemeredi

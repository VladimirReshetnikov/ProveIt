import GowersSzemeredi.Proofs18FejerIterationParameters
import GowersSzemeredi.Proofs18DensityIterationExponentialBudget
import GowersSzemeredi.Proofs18FiveTermUniformityParameters
import GowersSzemeredi.Proofs18FejerFiveTerm

/-! A fixed-power double-exponential bound for the complete five-term
iteration, with all density dependence and constants included. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

set_option exponentiation.threshold 2048 in
theorem fejer_five_term_step_threshold_le_double_exp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    intervalDiscrepancyStepThreshold 5 delta
      (fejerCubicDiscrepancyParameter (intervalUniformityParameter delta 5))
      (fejerCubicInverseThreshold (intervalUniformityParameter delta 5)) ≤
      Real.exp (Real.exp ((2 / intervalUniformityParameter delta 5) ^ ((2 : Nat) ^ 1086))) := by
  let alpha := intervalUniformityParameter delta 5
  let beta := fejerCubicDiscrepancyParameter alpha
  let x := 2 / alpha
  let p : Nat := 2 ^ 1086
  have hα : 0 < alpha := intervalUniformityParameter_pos hδ (by omega)
  have hα1 : alpha ≤ 1 := intervalUniformityParameter_le_one hδ.le hδone (by omega)
  have hb : 0 < beta := fejerCubicDiscrepancyParameter_pos hα
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hα1])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hδI : (delta ^ (5 : Nat))⁻¹ ≤ x := by
    have h := inv_anti₀ hα (intervalUniformityParameter_five_le_density_power hδ.le hδone)
    have hi : alpha⁻¹ ≤ x := by
      simpa only [one_div] using div_le_div_of_nonneg_right (by norm_num : (1 : Real) ≤ 2) hα.le
    exact h.trans hi
  have h32 : (32 : Real) ≤ x ^ (5 : Nat) :=
    (by norm_num : (32 : Real) ≤ (2 : Real) ^ (5 : Nat)).trans (pow_le_pow_left₀ (by norm_num) hx _)
  have hgain : 32 / beta ≤ x ^ p := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ x ^ (5 : Nat) * x ^ ((2 : Nat) ^ 59) := mul_le_mul h32
        (fejerCubicDiscrepancyParameter_inv_le_power hα hα1) (inv_nonneg.mpr hb.le) (by positivity)
      _ = x ^ (5 + (2 : Nat) ^ 59) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num [p])
  have hstop : (12801 : Real) / delta ^ (5 : Nat) ≤ x ^ p := by
    have hc : (12801 : Real) ≤ x ^ (14 : Nat) :=
      (by norm_num : (12801 : Real) ≤ (2 : Real) ^ (14 : Nat)).trans (pow_le_pow_left₀ (by norm_num) hx _)
    rw [div_eq_mul_inv]
    calc
      _ ≤ x ^ (14 : Nat) * x := mul_le_mul hc hδI (by positivity) (by positivity)
      _ = x ^ (15 : Nat) := (pow_succ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num [p])
  have h5 : (5 : Real) ≤ x ^ p := by
    have hh : (5 : Real) ≤ x ^ (3 : Nat) :=
      (by norm_num : (5 : Real) ≤ (2 : Real) ^ (3 : Nat)).trans (pow_le_pow_left₀ (by norm_num) hx _)
    exact hh.trans (pow_le_pow_right₀ hx1 (by norm_num [p]))
  norm_num only [intervalDiscrepancyStepThreshold, Nat.cast_ofNat, show (512 : Real) * 5 ^ (2 : Nat) + 1 = 12801 by norm_num]
  change max 5 (max (fejerCubicInverseThreshold alpha) (max (32 / beta) (12801 / delta ^ 5))) ≤ _
  exact max_le (h5.trans (real_le_double_exp _))
    (max_le (fejerCubicInverseThreshold_le_double_exp hα hα1)
      (max_le (hgain.trans (real_le_double_exp _)) (hstop.trans (real_le_double_exp _))))

set_option exponentiation.threshold 2048 in
theorem fejer_five_term_iteration_log_budget {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    let alpha := intervalUniformityParameter delta 5
    let beta := fejerCubicDiscrepancyParameter alpha
    let T := intervalDiscrepancyStepThreshold 5 delta beta (fejerCubicInverseThreshold alpha)
    let c := beta / (8 * boundaryRefinementConstant (beta / 64))
    1 + Real.log (max 1 T) + |Real.log c| ≤
      Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 1087)) := by
  let alpha := intervalUniformityParameter delta 5
  let beta := fejerCubicDiscrepancyParameter alpha
  let T := intervalDiscrepancyStepThreshold 5 delta beta (fejerCubicInverseThreshold alpha)
  let c := beta / (8 * boundaryRefinementConstant (beta / 64))
  let x := 2 / alpha
  let Y := x ^ ((2 : Nat) ^ 1086)
  have hα : 0 < alpha := intervalUniformityParameter_pos hδ (by omega)
  have hα1 : alpha ≤ 1 := intervalUniformityParameter_le_one hδ.le hδone (by omega)
  have hb : 0 < beta := fejerCubicDiscrepancyParameter_pos hα
  have hC : 0 < boundaryRefinementConstant (beta / 64) := section5LocalRefinementConstant_pos _ _
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := fejer_cubic_interval_length_factor_le_one hα hα1
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hα1])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hY : 1 ≤ Y := one_le_pow₀ hx1
  have hYe : Y ≤ Real.exp Y := by have h := Real.add_one_le_exp Y; linarith only [h]
  have h1 : (1 : Real) ≤ Real.exp Y := hY.trans hYe
  have hT : max 1 T ≤ Real.exp (Real.exp Y) := max_le
    (Real.one_le_exp_iff.mpr (Real.exp_pos _).le) (fejer_five_term_step_threshold_le_double_exp hδ hδone)
  have hlogT : Real.log (max 1 T) ≤ Real.exp Y :=
    (Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr hT
  have hlogc : |Real.log c| ≤ Real.exp Y := by
    calc
      _ = Real.log c⁻¹ := by rw [abs_of_nonpos (Real.log_nonpos hc.le hc1), Real.log_inv]
      _ ≤ c⁻¹ := Real.log_le_self (inv_nonneg.mpr hc.le)
      _ ≤ x ^ ((2 : Nat) ^ 1084) := fejer_cubic_interval_length_factor_inv_le_power hα hα1
      _ ≤ Y := pow_le_pow_right₀ hx1 (by norm_num : (2 : Nat) ^ 1084 ≤ (2 : Nat) ^ 1086)
      _ ≤ _ := hYe
  have h3 : (3 : Real) ≤ Real.exp (2 * Y) := by
    have h := Real.add_one_le_exp (2 * Y)
    linarith only [h, hY]
  have hinner : 3 * Y ≤ x ^ ((2 : Nat) ^ 1087) := by
    have hx2 : (3 : Real) ≤ x ^ (2 : Nat) := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hx 2
      norm_num at h
      linarith only [h]
    calc
      _ ≤ x ^ (2 : Nat) * x ^ ((2 : Nat) ^ 1086) := mul_le_mul_of_nonneg_right hx2 (by positivity)
      _ = x ^ (2 + (2 : Nat) ^ 1086) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num : 2 + (2 : Nat) ^ 1086 ≤ (2 : Nat) ^ 1087)
  change 1 + Real.log (max 1 T) + |Real.log c| ≤ _
  calc
    _ ≤ Real.exp Y + Real.exp Y + Real.exp Y := add_le_add (add_le_add h1 hlogT) hlogc
    _ = 3 * Real.exp Y := by ring
    _ ≤ Real.exp (2 * Y) * Real.exp Y := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = Real.exp (3 * Y) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr hinner

set_option exponentiation.threshold 2048 in
theorem fejerFiveTermThreshold_le_double_exp_alpha {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    fejerFiveTermThreshold delta ≤
      Real.exp (Real.exp ((2 / intervalUniformityParameter delta 5) ^ ((2 : Nat) ^ 1088))) := by
  have hα := intervalUniformityParameter_pos (k := 5) hδ (by omega)
  have hα1 := intervalUniformityParameter_le_one (k := 5) hδ.le hδone (by omega)
  have hx : 2 ≤ 2 / intervalUniformityParameter delta 5 := (le_div_iff₀ hα).mpr (by linarith only [hα1])
  have hg : 0 < fejerCubicDiscrepancyParameter (intervalUniformityParameter delta 5) / 8 :=
    div_pos (fejerCubicDiscrepancyParameter_pos hα) (by norm_num)
  have h := densityIterationClosedThreshold_le_double_exp_of_exp_budget _ _ _ _ _
    ((2 : Nat) ^ 60) ((2 : Nat) ^ 62) ((2 : Nat) ^ 1087) hg hx
    (fejer_five_term_iteration_log_budget hδ hδone)
    (fejer_cubic_gain_inv_le_power hα hα1) (fejer_cubic_iteration_base_le_exp hα hα1) (by norm_num)
  exact h.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith only [hx])
    (by norm_num : (2 : Nat) ^ 1087 + 1 ≤ (2 : Nat) ^ 1088))))

set_option exponentiation.threshold 2048 in
/-- The entire proved five-term construction has a conventional double
exponential bound in a fixed power of the reciprocal initial density. -/
theorem fejerFiveTermThreshold_le_double_exp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    fejerFiveTermThreshold delta ≤ Real.exp (Real.exp ((2 / delta) ^ ((2 : Nat) ^ 1097))) := by
  have hα := intervalUniformityParameter_pos (k := 5) hδ (by omega)
  apply (fejerFiveTermThreshold_le_double_exp_alpha hδ hδone).trans
  apply Real.exp_le_exp.mpr (Real.exp_le_exp.mpr _)
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ 2 / intervalUniformityParameter delta 5)
    (two_div_intervalUniformityParameter_five_le_power hδ hδone) ((2 : Nat) ^ 1088)
  rw [← pow_mul, show (512 : Nat) * (2 : Nat) ^ 1088 = (2 : Nat) ^ 1097 by norm_num] at h
  exact h

end LeanProofs.GowersSzemeredi

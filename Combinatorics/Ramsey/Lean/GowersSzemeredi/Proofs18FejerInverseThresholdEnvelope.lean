import GowersSzemeredi.Proofs18CubicRefinementConstantBounds
import GowersSzemeredi.Proofs18FejerSharperPrimeThreshold
import GowersSzemeredi.Proofs18FejerCubicDiscrepancy

/-! A conventional double-exponential threshold for the full improved
cubic inverse theorem, including untwisting and all fixed constants.

`fejer_cubic_function_discrepancy_bound_double_exp` is in
`Proofs18FejerInverseThresholdEnvelopeSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem fejerCubicDiscrepancyExponent_inv_le_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (fejerCubicDiscrepancyExponent alpha)⁻¹ ≤
      Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 61)) := by
  let x := 2 / alpha
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have he : 0 < fejerCubicLocalizationExponent alpha := Real.rpow_pos_of_pos (by norm_num) _
  have ht := (fejerCubicLocalCountExponent_bounds hα hαone).1
  have hK : 2 * (polynomialPartitionConstant 3 : Real) ≤ x ^ (23 : Nat) :=
    (by norm_num [polynomialPartitionConstant] : 2 * (polynomialPartitionConstant 3 : Real) ≤
      (2 : Real) ^ (23 : Nat)).trans (pow_le_pow_left₀ (by norm_num) hx _)
  have hpoly : 2 * (polynomialPartitionConstant 3 : Real) * (fejerCubicLocalCountExponent alpha)⁻¹ ≤
      x ^ ((2 : Nat) ^ 60) :=
    (mul_le_mul hK (fejerCubicLocalCountExponent_inv_le_power hα hαone) (inv_nonneg.mpr ht.le)
      (by positivity)).trans ((pow_add _ _ _).symm.trans_le (pow_le_pow_right₀ hx1 (by norm_num)))
  have heI : (fejerCubicLocalizationExponent alpha)⁻¹ ≤ Real.exp (x ^ ((2 : Nat) ^ 60)) :=
    (fejerCubicLocalizationExponent_inv_le_exp hα).trans
      (Real.exp_le_exp.mpr (pow_le_pow_right₀ hx1 (by norm_num)))
  have hY : 2 ≤ x ^ ((2 : Nat) ^ 60) := hx.trans (le_self_pow₀ hx1 (by positivity))
  rw [fejerCubicDiscrepancyExponent, inv_div, div_eq_mul_inv, mul_inv_rev, ← mul_assoc]
  calc _ ≤ x ^ ((2 : Nat) ^ 60) * Real.exp (x ^ ((2 : Nat) ^ 60)) :=
        mul_le_mul hpoly heI (inv_nonneg.mpr he.le) (by positivity)
    _ ≤ Real.exp (x ^ ((2 : Nat) ^ 60)) * Real.exp (x ^ ((2 : Nat) ^ 60)) := by
        gcongr; linarith only [Real.add_one_le_exp (x ^ ((2 : Nat) ^ 60))]
    _ ≤ Real.exp (x ^ ((2 : Nat) ^ 61)) := by
        rw [← Real.exp_add, ← two_mul, pow_succ 2 60, pow_mul, sq]
        gcongr

set_option exponentiation.threshold 2048 in
/-- The variable cubic phase-refinement constant is polynomial in the
reciprocal uniformity parameter, with an explicit fixed exponent. -/
theorem fejerCubicPhaseRefinementConstant_le_power {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    fejerCubicPhaseRefinementConstant alpha ≤ (2 / alpha) ^ ((2 : Nat) ^ 1085) := by
  let x := 2 / alpha
  let beta := fejerCubicTwistedDiscrepancyParameter alpha
  let D := fejerCubicTwistedCountConstant alpha
  let K := polynomialPartitionConstant 3
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hb : 0 < beta :=
    (div_pos_iff_of_pos_right two_pos).mp (fejerCubicDiscrepancyParameter_pos hα)
  have hβI : beta⁻¹ ≤ x ^ ((2 : Nat) ^ 59) :=
    (inv_anti₀ (fejerCubicDiscrepancyParameter_pos hα) (div_le_self hb.le (by norm_num))).trans
      (fejerCubicDiscrepancyParameter_inv_le_power hα hαone)
  have hC := section5LocalRefinementConstant_le_scaled 3 beta (x ^ ((2 : Nat) ^ 59))
    hb (one_le_pow₀ hx1) hβI
  have hCfixed : section5LocalRefinementConstant 3 1 ≤ x ^ ((2 : Nat) ^ 1082) :=
    (section5_degree_le_three_refinement_constant_upper (by omega)).trans
      (pow_le_pow_left₀ (by norm_num) hx _)
  have hD : D ≤ x ^ ((2 : Nat) ^ 1084) :=
    (fejerCubicTwistedCountConstant_upper hα hαone).trans (pow_le_pow_left₀ (by norm_num) hx _)
  have hD0 : 0 ≤ D := by
    dsimp [D, fejerCubicTwistedCountConstant, fejerCubicLocalCountConstant]; positivity
  have hKpos : (0 : Real) < K := by norm_num [K, polynomialPartitionConstant]
  have hKi : (K : Real)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by norm_num [K, polynomialPartitionConstant])
  have hroot : D ^ (K : Real)⁻¹ ≤ x ^ ((2 : Nat) ^ 1084) :=
    (Real.rpow_le_rpow hD0 hD (inv_nonneg.mpr hKpos.le)).trans
      ((Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hx1) hKi).trans_eq (Real.rpow_one _))
  change section5LocalRefinementConstant 3 beta * D ^ (K : Real)⁻¹ ≤ _
  calc _ ≤ x ^ ((2 : Nat) ^ 1082) * (x ^ ((2 : Nat) ^ 59)) ^ K * x ^ ((2 : Nat) ^ 1084) :=
        mul_le_mul (hC.trans (mul_le_mul_of_nonneg_right hCfixed (by positivity))) hroot
          (Real.rpow_nonneg hD0 _) (by positivity)
    _ = x ^ ((2 : Nat) ^ 1082 + (2 : Nat) ^ 59 * K + (2 : Nat) ^ 1084) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num [K, polynomialPartitionConstant])

set_option exponentiation.threshold 2048 in
/-- Every threshold in the full cubic inverse theorem is bounded by one
conventional double exponential, with all constants independent of alpha. -/
theorem fejerCubicInverseThreshold_le_double_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    fejerCubicInverseThreshold alpha ≤ Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 62))) := by
  let x := 2 / alpha
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hC : fejerCubicPhaseRefinementConstant alpha ≤ Real.exp (Real.exp (x ^ ((2 : Nat) ^ 61))) :=
    (fejerCubicPhaseRefinementConstant_le_power hα hαone).trans
      ((pow_two_pow_le_exp_pow_succ hx 1085).trans (Real.exp_le_exp.mpr
        ((pow_le_pow_right₀ hx1 (by norm_num : 1085 + 1 ≤ (2 : Nat) ^ 61)).trans
          (by linarith only [Real.add_one_le_exp (x ^ ((2 : Nat) ^ 61))]))))
  have hinner : x ^ ((2 : Nat) ^ 61) + x ^ ((2 : Nat) ^ 61) ≤ x ^ ((2 : Nat) ^ 62) := by
    rw [← two_mul, pow_succ 2 61, pow_mul, sq]
    exact mul_le_mul_of_nonneg_right (hx.trans (le_self_pow₀ hx1 (by positivity))) (by positivity)
  exact max_le ((fejerCubicTwistedThreshold_le_double_exp_sharp hα hαone).trans
    (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (pow_le_pow_right₀ hx1 (by norm_num)))))
    ((positivePowerThreshold_one_le_double_exp (fejerCubicDiscrepancyExponent_pos hα hαone).le hC
      (fejerCubicDiscrepancyExponent_inv_le_exp hα hαone)).trans
      (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hinner)))

end LeanProofs.GowersSzemeredi

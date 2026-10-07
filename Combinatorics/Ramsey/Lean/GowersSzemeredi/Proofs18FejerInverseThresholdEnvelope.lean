import GowersSzemeredi.Proofs18CubicRefinementConstantBounds
import GowersSzemeredi.Proofs18FejerCubicDiscrepancy

/-! A conventional double-exponential threshold for the full improved
cubic inverse theorem, including untwisting and all fixed constants. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem fejerCubicDiscrepancyExponent_inv_le_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (fejerCubicDiscrepancyExponent alpha)⁻¹ ≤
      Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 61)) := by
  let x := 2 / alpha
  let e := fejerCubicLocalizationExponent alpha
  let t := fejerCubicLocalCountExponent alpha
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have he : 0 < e := by dsimp [e, fejerCubicLocalizationExponent]; positivity
  have ht : 0 < t := (fejerCubicLocalCountExponent_bounds hα hαone).1
  have hK : 2 * (polynomialPartitionConstant 3 : Real) ≤ x ^ (23 : Nat) := by
    exact (by norm_num [polynomialPartitionConstant] : 2 * (polynomialPartitionConstant 3 : Real) ≤ (2 : Real) ^ (23 : Nat)).trans
      (pow_le_pow_left₀ (by norm_num) hx _)
  have hpoly : (2 * (polynomialPartitionConstant 3 : Real)) * t⁻¹ ≤ x ^ ((2 : Nat) ^ 60) := by
    calc
      _ ≤ x ^ (23 : Nat) * x ^ ((2 : Nat) ^ 59) :=
        mul_le_mul hK (fejerCubicLocalCountExponent_inv_le_power hα hαone) (inv_nonneg.mpr ht.le) (pow_nonneg hx0 _)
      _ = x ^ (23 + (2 : Nat) ^ 59) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num)
  have heI : e⁻¹ ≤ Real.exp (x ^ ((2 : Nat) ^ 60)) :=
    (fejerCubicLocalizationExponent_inv_le_exp hα).trans
      (Real.exp_le_exp.mpr (pow_le_pow_right₀ hx1 (by norm_num : (2 : Nat) ^ 53 ≤ (2 : Nat) ^ 60)))
  have hlin : x ^ ((2 : Nat) ^ 60) ≤ Real.exp (x ^ ((2 : Nat) ^ 60)) := by
    have h := Real.add_one_le_exp (x ^ ((2 : Nat) ^ 60))
    linarith only [h]
  change ((e * t) / (2 * (polynomialPartitionConstant 3 : Real)))⁻¹ ≤ _
  rw [inv_div, div_eq_mul_inv, mul_inv_rev, ← mul_assoc]
  calc
    _ ≤ x ^ ((2 : Nat) ^ 60) * Real.exp (x ^ ((2 : Nat) ^ 60)) :=
      mul_le_mul hpoly heI (inv_nonneg.mpr he.le) (pow_nonneg hx0 _)
    _ ≤ Real.exp (x ^ ((2 : Nat) ^ 60)) * Real.exp (x ^ ((2 : Nat) ^ 60)) :=
      mul_le_mul_of_nonneg_right hlin (Real.exp_pos _).le
    _ = Real.exp (2 * x ^ ((2 : Nat) ^ 60)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ x * x ^ ((2 : Nat) ^ 60) := mul_le_mul_of_nonneg_right hx (pow_nonneg hx0 _)
        _ = x ^ ((2 : Nat) ^ 60 + 1) := (pow_succ' _ _).symm
        _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num)

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
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hb : 0 < beta := by
    have h := fejerCubicDiscrepancyParameter_pos hα
    change 0 < beta / 2 at h
    linarith only [h]
  have hβle : fejerCubicDiscrepancyParameter alpha ≤ beta := div_le_self hb.le (by norm_num)
  have hβI : beta⁻¹ ≤ x ^ ((2 : Nat) ^ 59) :=
    (inv_anti₀ (fejerCubicDiscrepancyParameter_pos hα) hβle).trans
      (fejerCubicDiscrepancyParameter_inv_le_power hα hαone)
  have hC := section5LocalRefinementConstant_le_scaled 3 beta (x ^ ((2 : Nat) ^ 59))
    hb (one_le_pow₀ hx1) hβI
  have hCfixed : section5LocalRefinementConstant 3 1 ≤ x ^ ((2 : Nat) ^ 1082) :=
    (section5_degree_le_three_refinement_constant_upper (by omega)).trans
      (pow_le_pow_left₀ (by norm_num) hx _)
  have hD : D ≤ x ^ ((2 : Nat) ^ 1084) :=
    (fejerCubicTwistedCountConstant_upper hα hαone).trans (pow_le_pow_left₀ (by norm_num) hx _)
  have hD0 : 0 ≤ D := by dsimp [D, fejerCubicTwistedCountConstant, fejerCubicLocalCountConstant]; positivity
  have hKpos : (0 : Real) < K := by norm_num [K, polynomialPartitionConstant]
  have hKi : (K : Real)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by norm_num [K, polynomialPartitionConstant])
  have hroot : D ^ (K : Real)⁻¹ ≤ x ^ ((2 : Nat) ^ 1084) := by
    calc
      _ ≤ (x ^ ((2 : Nat) ^ 1084)) ^ (K : Real)⁻¹ := Real.rpow_le_rpow hD0 hD (inv_nonneg.mpr hKpos.le)
      _ ≤ _ := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hx1) hKi
  change section5LocalRefinementConstant 3 beta * D ^ (K : Real)⁻¹ ≤ _
  calc
    _ ≤ (section5LocalRefinementConstant 3 1 * (x ^ ((2 : Nat) ^ 59)) ^ K) * x ^ ((2 : Nat) ^ 1084) :=
      mul_le_mul hC hroot (Real.rpow_nonneg hD0 _)
        (mul_nonneg (section5LocalRefinementConstant_pos 3 1).le (pow_nonneg (pow_nonneg hx0 _) _))
    _ ≤ (x ^ ((2 : Nat) ^ 1082) * (x ^ ((2 : Nat) ^ 59)) ^ K) * x ^ ((2 : Nat) ^ 1084) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCfixed (by positivity)) (pow_nonneg hx0 _)
    _ = x ^ ((2 : Nat) ^ 1082 + (2 : Nat) ^ 59 * K + (2 : Nat) ^ 1084) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num [K, polynomialPartitionConstant])

set_option exponentiation.threshold 2048 in
/-- Every threshold in the full cubic inverse theorem is bounded by one
conventional double exponential, with all constants independent of alpha. -/
theorem fejerCubicInverseThreshold_le_double_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    fejerCubicInverseThreshold alpha ≤ Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 1086))) := by
  let x := 2 / alpha
  let A := x ^ ((2 : Nat) ^ 1085)
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hA0 : 0 ≤ A := pow_nonneg (by linarith only [hx]) _
  have hAexp : A ≤ Real.exp A := by have h := Real.add_one_le_exp A; linarith only [h]
  have hC : fejerCubicPhaseRefinementConstant alpha ≤ Real.exp (1 * A) := by
    rw [one_mul]
    exact (fejerCubicPhaseRefinementConstant_le_power hα hαone).trans hAexp
  have hD : (1 : Real)⁻¹ ≤ Real.exp (1 * A) := by
    simpa only [one_mul, inv_one] using Real.one_le_exp_iff.mpr hA0
  have heI : (fejerCubicDiscrepancyExponent alpha)⁻¹ ≤ Real.exp (1 * A) := by
    rw [one_mul]
    exact (fejerCubicDiscrepancyExponent_inv_le_exp hα hαone).trans
      (Real.exp_le_exp.mpr (pow_le_pow_right₀ hx1 (by norm_num : (2 : Nat) ^ 61 ≤ (2 : Nat) ^ 1085)))
  have hp := positivePowerThreshold_le_double_exp zero_lt_one
    (fejerCubicDiscrepancyExponent_pos hα hαone).le hA0
    (by norm_num : (0 : Real) ≤ 1) (by norm_num : (0 : Real) ≤ 1) hC hD heI
  norm_num only [show (1 + 1 + 1 : Real) = 3 by norm_num] at hp
  have hinner : 3 * A ≤ x ^ ((2 : Nat) ^ 1086) := by
    have hx2 : (3 : Real) ≤ x ^ (2 : Nat) := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hx 2
      norm_num at h
      linarith only [h]
    calc
      _ ≤ x ^ (2 : Nat) * x ^ ((2 : Nat) ^ 1085) := mul_le_mul_of_nonneg_right hx2 hA0
      _ = x ^ (2 + (2 : Nat) ^ 1085) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num : 2 + (2 : Nat) ^ 1085 ≤ (2 : Nat) ^ 1086)
  unfold fejerCubicInverseThreshold
  apply max_le
  · exact (fejerCubicTwistedThreshold_le_double_exp hα hαone).trans
      (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (pow_le_pow_right₀ hx1
        (by norm_num : (2 : Nat) ^ 324 ≤ (2 : Nat) ^ 1086))))
  · exact hp.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hinner))

/-- The complete improved cubic inverse interface at its conventional
numerical threshold, ready for the density-increment iteration. -/
theorem fejer_cubic_function_discrepancy_bound_double_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    FunctionDiscrepancyBound 3 alpha (fejerCubicDiscrepancyParameter alpha)
      (fejerCubicDiscrepancyExponent alpha)
      (Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 1086)))) := by
  intro N _ _ hN f hf hnot
  exact fejer_cubic_function_discrepancy_bound hα hαone N
    ((fejerCubicInverseThreshold_le_double_exp hα hαone).trans hN) f hf hnot

end LeanProofs.GowersSzemeredi

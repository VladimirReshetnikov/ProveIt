import GowersSzemeredi.Proofs18QuadraticThreshold
import GowersSzemeredi.Proofs05RefinementConstantBounds

/-! A single-exponential bound with fixed power dependence on inverse
nonuniformity for the explicit quadratic density-increment threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Elementary lower bounds for the two quadratic parameters by powers of
alpha/2. They avoid absorbing any alpha-dependent quantity into a constant. -/
theorem quadratic_parameters_lower {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (alpha / 2) ^ (12380 : Nat) ≤
      (2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat) ∧
    (alpha / 2) ^ (24744 : Nat) ≤ quadraticDiscrepancyExponent alpha := by
  constructor
  · rw [show (12380 : Nat) = 19 + 2 + 12359 from rfl, pow_add, pow_add, zpow_neg, zpow_ofNat,
      ← inv_pow, ← one_div]
    gcongr
    linarith
  · unfold quadraticDiscrepancyExponent cor711Exponent
    rw [show (24744 : Nat) = 26 + 12359 * 2 from rfl, pow_add, pow_mul, Nat.cast_one, inv_one,
      mul_one, mul_div_right_comm]
    gcongr
    calc (alpha / 2) ^ 26 ≤ (1 / 2) ^ 26 := by gcongr
      _ = _ := by norm_num [Real.rpow_neg]

/-- The inverse parameters have fixed-power upper bounds in 2/alpha. -/
theorem quadratic_parameters_inv_upper {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    ((2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat))⁻¹ ≤
      (2 / alpha) ^ (12380 : Nat) ∧
    (quadraticDiscrepancyExponent alpha)⁻¹ ≤ (2 / alpha) ^ (24744 : Nat) := by
  obtain ⟨hb, hs⟩ := quadratic_parameters_lower hα hαone
  have ha : 0 < alpha / 2 := by positivity
  have hβ : 0 < (2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat) := by positivity
  have hσ : 0 < quadraticDiscrepancyExponent alpha := (pow_pos ha _).trans_le hs
  constructor
  · calc
      _ ≤ ((alpha / 2) ^ (12380 : Nat))⁻¹ := (inv_le_inv₀ hβ (pow_pos ha _)).2 hb
      _ = _ := by rw [← inv_pow, inv_div]
  · calc
      _ ≤ ((alpha / 2) ^ (24744 : Nat))⁻¹ := (inv_le_inv₀ hσ (pow_pos ha _)).2 hs
      _ = _ := by rw [← inv_pow, inv_div]

/-- Uniform polynomial upper bound for the quadratic refinement constant. -/
theorem quadraticRefinementConstant_le_power {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    quadraticRefinementConstant alpha ≤
      (6 * section5LocalRefinementConstant 2 1) * (2 / alpha) ^ (12380 * 2048 : Nat) := by
  let u : Real := 2 / alpha
  let beta := (2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat)
  have hu : 1 ≤ u := (le_div_iff₀ hα).2 (by linarith only [hαone])
  have hβ : 0 < beta := by dsimp [beta]; positivity
  have hbase := section5LocalRefinementConstant_le_scaled 2 beta (u ^ (12380 : Nat))
    hβ (one_le_pow₀ hu) (quadratic_parameters_inv_upper hα hαone).1
  have hK : polynomialPartitionConstant 2 = 2048 := by norm_num [polynomialPartitionConstant, Nat.factorial]
  have hsix : (6 : Real) ^ (1 / 2048 : Real) ≤ 6 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 6)
      (by norm_num : (1 / 2048 : Real) ≤ 1)
  change section5LocalRefinementConstant 2 beta * (6 : Real) ^ (1 / 2048 : Real) ≤ _
  calc
    _ ≤ (section5LocalRefinementConstant 2 1 * (u ^ (12380 : Nat)) ^ polynomialPartitionConstant 2) * 6 :=
      mul_le_mul hbase hsix (Real.rpow_nonneg (by norm_num) _)
        (mul_nonneg (section5LocalRefinementConstant_pos 2 1).le
          (pow_nonneg (pow_nonneg (zero_le_one.trans hu) _) _))
    _ = _ := by
      rw [hK, ← pow_mul]
      generalize u ^ (12380 * 2048 : Nat) = t
      ring

/-- A fixed constant and fixed exponent bound the entire starting threshold. -/
theorem quadraticDensityThreshold_le_exp_power {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    quadraticDensityThreshold alpha ≤
      Real.exp ((4 + 6 * section5LocalRefinementConstant 2 1) *
        (2 / alpha) ^ (12380 * 2048 + 24744 : Nat)) := by
  have hpow : 1 ≤ (2 / alpha) ^ (12380 * 2048 : Nat) :=
    one_le_pow₀ ((le_div_iff₀ hα).2 (by linarith only [hαone]))
  have hC := quadraticRefinementConstant_le_power hα hαone
  have hσ : 0 < quadraticDiscrepancyExponent alpha :=
    div_pos (quadratic_frequency_exponent_bounds hα hαone).1 (by norm_num)
  have hD := section5LocalRefinementConstant_pos 2 1
  refine (quadraticDensityThreshold_le_exp alpha hα hαone).trans (Real.exp_le_exp.mpr ?_)
  rw [div_eq_mul_inv, pow_add, ← mul_assoc]
  refine mul_le_mul ?_ (quadratic_parameters_inv_upper hα hαone).2 (by positivity) (by positivity)
  generalize (2 / alpha) ^ (12380 * 2048 : Nat) = P at hpow hC ⊢
  linarith

end LeanProofs.GowersSzemeredi

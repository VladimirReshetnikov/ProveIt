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
  let a := alpha / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hahalf : a ≤ 1 / 2 := by dsimp [a]; linarith only [hαone]
  have haα : a ≤ alpha := by dsimp [a]; linarith only [hα]
  have hc19 : a ^ (19 : Nat) ≤ (2 : Real) ^ (-(19 : Int)) := by
    calc
      _ ≤ (1 / 2 : Real) ^ (19 : Nat) := pow_le_pow_left₀ ha hahalf _
      _ = _ := by norm_num
  have hc26 : a ^ (26 : Nat) ≤ (2 : Real) ^ (-(26 : Int)) := by
    calc
      _ ≤ (1 / 2 : Real) ^ (26 : Nat) := pow_le_pow_left₀ ha hahalf _
      _ = _ := by norm_num
  constructor
  · calc
      a ^ (12380 : Nat) = a ^ (19 : Nat) * a ^ (2 : Nat) * a ^ (12359 : Nat) := by
        rw [← pow_add, ← pow_add]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul hc19 (pow_le_pow_left₀ ha haα 2) (pow_nonneg ha _) (by positivity))
        (pow_nonneg ha _)
  · have hs : quadraticDiscrepancyExponent alpha =
        (2 : Real) ^ (-(26 : Int)) * a ^ (24718 : Nat) := by
      unfold quadraticDiscrepancyExponent cor711Exponent
      simp only [Nat.cast_one, inv_one, mul_one]
      change ((2 : Real) ^ (-(14 : Real)) * (a ^ (12359 : Nat)) ^ 2) / 4096 = _
      rw [← pow_mul]
      norm_num [Real.rpow_neg]
      generalize a ^ (24718 : Nat) = t
      ring
    rw [hs]
    calc
      a ^ (24744 : Nat) = a ^ (26 : Nat) * a ^ (24718 : Nat) := by rw [← pow_add]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc26 (pow_nonneg ha _)

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
  let u : Real := 2 / alpha
  let D : Real := 6 * section5LocalRefinementConstant 2 1
  have hu : 1 ≤ u := (le_div_iff₀ hα).2 (by linarith only [hαone])
  have hD : 0 < D := mul_pos (by norm_num) (section5LocalRefinementConstant_pos _ _)
  have hpow : 1 ≤ u ^ (12380 * 2048 : Nat) := one_le_pow₀ hu
  have hC := quadraticRefinementConstant_le_power hα hαone
  have hinv := (quadratic_parameters_inv_upper hα hαone).2
  have hσ : 0 < quadraticDiscrepancyExponent alpha :=
    div_pos (quadratic_frequency_exponent_bounds hα hαone).1 (by norm_num)
  apply (quadraticDensityThreshold_le_exp alpha hα hαone).trans
  apply Real.exp_le_exp.mpr
  rw [div_eq_mul_inv]
  have hsum : 4 + quadraticRefinementConstant alpha ≤ (4 + D) * u ^ (12380 * 2048 : Nat) := by
    have h4 : (4 : Real) ≤ 4 * u ^ (12380 * 2048 : Nat) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : Real) ≤ 4)
    calc
      _ ≤ 4 * u ^ (12380 * 2048 : Nat) + D * u ^ (12380 * 2048 : Nat) := add_le_add h4 hC
      _ = _ := by rw [add_mul]
  calc
    _ ≤ ((4 + D) * u ^ (12380 * 2048 : Nat)) * u ^ (24744 : Nat) :=
      mul_le_mul hsum hinv (inv_nonneg.mpr hσ.le) (by positivity)
    _ = _ := by rw [mul_assoc, ← pow_add]

end LeanProofs.GowersSzemeredi

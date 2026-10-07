import GowersSzemeredi.Proofs18FejerCubicParameters
import GowersSzemeredi.Proofs18QuadraticIterationParameters
import GowersSzemeredi.Proofs13FourierThresholdEnvelope

/-! Polynomial reciprocal budgets for the improved cubic discrepancy
parameters and their local quadratic models. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Absorb a fixed dyadic coefficient and the two density factors into
one power of the reciprocal uniformity parameter. -/
theorem scaled_cubic_density_inv_le {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (c n : Nat) :
    ((2 : Real) ^ (-(c : Int)) * alpha ^ 2 * (alpha / 2) ^ n)⁻¹ ≤
      (2 / alpha) ^ (c + 2 + n) := by
  let x := 2 / alpha
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hi : alpha⁻¹ ≤ x := by
    simpa only [one_div] using div_le_div_of_nonneg_right (by norm_num : (1 : Real) ≤ 2) hα.le
  have hai : (alpha / 2)⁻¹ = x := by dsimp [x]; rw [inv_div]
  calc
    _ = x ^ n * (alpha⁻¹) ^ (2 : Nat) * (2 : Real) ^ c := by
      rw [mul_inv_rev, mul_inv_rev, ← inv_pow, ← inv_pow, hai, zpow_neg, inv_inv, zpow_natCast]
      ring
    _ ≤ x ^ n * x ^ (2 : Nat) * x ^ c := mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hα.le) hi 2) (pow_nonneg hx0 _))
      (pow_le_pow_left₀ (by norm_num) hx c) (by positivity) (by positivity)
    _ = _ := by rw [pow_add, pow_add]; ring

theorem fejerCubicLocalQuadraticParameter_inv_le_power {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (fejerCubicLocalQuadraticParameter alpha)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 43) := by
  have hx : 1 ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  exact (scaled_cubic_density_inv_le hα hαone 71 ((2 : Nat) ^ 42)).trans
    (pow_le_pow_right₀ hx (by norm_num))

theorem fejerCubicLocalizedMassParameter_inv_le_power {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (fejerCubicLocalizedMassParameter alpha)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 43) := by
  have hx : 1 ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  exact (scaled_cubic_density_inv_le hα hαone 59 ((2 : Nat) ^ 42)).trans
    (pow_le_pow_right₀ hx (by norm_num))

theorem two_div_fejerCubicLocalQuadraticParameter_le_power {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    2 / fejerCubicLocalQuadraticParameter alpha ≤ (2 / alpha) ^ ((2 : Nat) ^ 43 + 1) := by
  have hx : 2 ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  rw [div_eq_mul_inv, pow_succ']
  exact mul_le_mul hx (fejerCubicLocalQuadraticParameter_inv_le_power hα hαone)
    (inv_nonneg.mpr (fejerCubicLocalQuadraticParameter_pos hα).le) (by positivity)

theorem fejerCubicLocalCountExponent_inv_le_power {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (fejerCubicLocalCountExponent alpha)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 59) := by
  have ha := fejerCubicLocalQuadraticParameter_pos hα
  have ha1 := fejerCubicLocalQuadraticParameter_le_one hα.le hαone
  have hx : 1 ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hi := (quadratic_interval_parameters_inv_upper ha ha1).2.2.1
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2 / fejerCubicLocalQuadraticParameter alpha)
    (two_div_fejerCubicLocalQuadraticParameter_le_power hα hαone) 24748
  rw [← pow_mul] at hp
  exact hi.trans (hp.trans (pow_le_pow_right₀ hx (by norm_num)))

theorem fejerCubicDiscrepancyParameter_inv_le_power {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (fejerCubicDiscrepancyParameter alpha)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 59) := by
  let x := 2 / alpha
  let a := fejerCubicLocalQuadraticParameter alpha
  let mu := fejerCubicLocalizedMassParameter alpha
  have ha : 0 < a := fejerCubicLocalQuadraticParameter_pos hα
  have ha1 : a ≤ 1 := fejerCubicLocalQuadraticParameter_le_one hα.le hαone
  have hm : 0 < mu := by dsimp [mu, fejerCubicLocalizedMassParameter]; positivity
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hquad := (quadratic_interval_parameters_inv_upper ha ha1).1
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2 / a)
    (two_div_fejerCubicLocalQuadraticParameter_le_power hα hαone) 12381
  rw [← pow_mul] at hp
  have hb : 0 < quadraticDiscrepancyParameter a := by unfold quadraticDiscrepancyParameter; positivity
  have hβ : (quadraticDiscrepancyParameter a)⁻¹ ≤ x ^ (((2 : Nat) ^ 43 + 1) * 12381) := hquad.trans hp
  change (mu * quadraticDiscrepancyParameter a / 2)⁻¹ ≤ _
  rw [inv_div, div_eq_mul_inv, mul_inv_rev]
  calc
    _ ≤ x * (x ^ (((2 : Nat) ^ 43 + 1) * 12381) * x ^ ((2 : Nat) ^ 43)) :=
      mul_le_mul hx (mul_le_mul hβ (fejerCubicLocalizedMassParameter_inv_le_power hα hαone)
        (inv_nonneg.mpr hm.le) (pow_nonneg hx0 _)) (by positivity) hx0
    _ = x ^ (1 + (((2 : Nat) ^ 43 + 1) * 12381) + (2 : Nat) ^ 43) := by
      rw [pow_add, pow_add, pow_one, mul_assoc]
    _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num)

theorem fejerCubicLocalizationExponent_inv_le_exp {alpha : Real}
    (hα : 0 < alpha) :
    (fejerCubicLocalizationExponent alpha)⁻¹ ≤ Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 53)) := by
  unfold fejerCubicLocalizationExponent
  rw [← Real.inv_rpow (by norm_num : (0 : Real) ≤ 1 / 2)]
  norm_num only [one_div, inv_inv]
  exact two_rpow_le_exp (pow_nonneg (by positivity) _)

end LeanProofs.GowersSzemeredi

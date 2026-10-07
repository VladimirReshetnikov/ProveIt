import GowersSzemeredi.Proofs18FejerCubicParameters

/-! Strict improvements in both cubic inverse parameters, for every alpha in (0,1].
These comparisons concern the proved discrepancy and average-size parameters;
no comparison of the full five-term starting thresholds is inferred. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem quadraticDiscrepancyParameter_mono {a b : Real} (ha : 0 ≤ a) (hab : a ≤ b) :
    quadraticDiscrepancyParameter a ≤ quadraticDiscrepancyParameter b := by
  unfold quadraticDiscrepancyParameter
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab 2) (by positivity))
    (pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hab (by norm_num)) _)
    (by positivity) (by positivity)

theorem quadraticDiscrepancyExponent_mono {a b : Real} (ha : 0 ≤ a) (hab : a ≤ b) :
    quadraticDiscrepancyExponent a ≤ quadraticDiscrepancyExponent b := by
  unfold quadraticDiscrepancyExponent cor711Exponent
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by positivity)
    (pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hab (by norm_num)) _) _

theorem cubic_density_power_lt_fejer {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (alpha / 2) ^ ((2 : Nat) ^ 76) < (alpha / 2) ^ ((2 : Nat) ^ 42) := by
  exact pow_lt_pow_right_of_lt_one₀ (by positivity) (by linarith only [hαone])
    (by norm_num : (2 : Nat) ^ 42 < (2 : Nat) ^ 76)

theorem cubicLocalQuadraticParameter_lt_fejer {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    cubicLocalQuadraticParameter alpha < fejerCubicLocalQuadraticParameter alpha := by
  unfold cubicLocalQuadraticParameter fejerCubicLocalQuadraticParameter
  exact mul_lt_mul_of_pos_left (cubic_density_power_lt_fejer hα hαone) (by positivity)

theorem cubicLocalizedMassParameter_lt_fejer {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    cubicLocalizedMassParameter alpha < fejerCubicLocalizedMassParameter alpha := by
  unfold cubicLocalizedMassParameter fejerCubicLocalizedMassParameter
  exact mul_lt_mul_of_pos_left (cubic_density_power_lt_fejer hα hαone) (by positivity)

theorem cubicLocalizationExponent_lt_fejer {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    cubicLocalizationExponent alpha < fejerCubicLocalizationExponent alpha := by
  have ht : (1 : Real) < 2 / alpha := (lt_div_iff₀ hα).mpr (by linarith only [hαone])
  exact Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num)
    (pow_lt_pow_right₀ ht (by norm_num : (2 : Nat) ^ 53 < (2 : Nat) ^ 88))

/-- Retaining the Fejer Fourier parameters strictly increases the exponent
of the average cell size guaranteed by the full cubic inverse theorem. -/
theorem cubicDiscrepancyExponent_lt_fejer {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    cubicDiscrepancyExponent alpha < fejerCubicDiscrepancyExponent alpha := by
  have ha := cubicLocalQuadraticParameter_pos hα
  have hab := (cubicLocalQuadraticParameter_lt_fejer hα hαone).le
  have ht : cubicLocalCountExponent alpha ≤ fejerCubicLocalCountExponent alpha :=
    div_le_div_of_nonneg_right (quadraticDiscrepancyExponent_mono ha.le hab) (by norm_num)
  have htpos := (cubicLocalCountExponent_bounds hα hαone).1
  have hepos : 0 < fejerCubicLocalizationExponent alpha := by
    unfold fejerCubicLocalizationExponent
    positivity
  unfold cubicDiscrepancyExponent fejerCubicDiscrepancyExponent
  apply div_lt_div_of_pos_right _ (by unfold polynomialPartitionConstant; positivity)
  exact (mul_lt_mul_of_pos_right (cubicLocalizationExponent_lt_fejer hα hαone) htpos).trans_le
    (mul_le_mul_of_nonneg_left ht hepos.le)

/-- The same stronger Fourier extraction strictly increases the surviving
normalized discrepancy in the complete, untwisted cubic partition. -/
theorem cubicDiscrepancyParameter_lt_fejer {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    cubicDiscrepancyParameter alpha < fejerCubicDiscrepancyParameter alpha := by
  have ha := cubicLocalQuadraticParameter_pos hα
  have hb : 0 < quadraticDiscrepancyParameter (cubicLocalQuadraticParameter alpha) := by
    unfold quadraticDiscrepancyParameter
    positivity
  have hab := quadraticDiscrepancyParameter_mono ha.le
    (cubicLocalQuadraticParameter_lt_fejer hα hαone).le
  have hmu : 0 ≤ fejerCubicLocalizedMassParameter alpha := by
    unfold fejerCubicLocalizedMassParameter
    positivity
  unfold cubicDiscrepancyParameter fejerCubicDiscrepancyParameter
    cubicTwistedDiscrepancyParameter fejerCubicTwistedDiscrepancyParameter
  apply div_lt_div_of_pos_right _ (by norm_num)
  exact (mul_lt_mul_of_pos_right (cubicLocalizedMassParameter_lt_fejer hα hαone) hb).trans_le
    (mul_le_mul_of_nonneg_left hab hmu)

end LeanProofs.GowersSzemeredi

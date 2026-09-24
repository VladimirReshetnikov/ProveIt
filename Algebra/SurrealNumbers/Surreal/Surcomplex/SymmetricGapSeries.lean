import Surreal.Surcomplex.AcosEndpointSeries
import Surreal.Foundations.SignSequenceBinomial
import Surreal.Foundations.SignSequenceRelativeAsymptotics

/-!
# Strong series for a symmetric infinitesimal side gap

These are the three complete normalized strong series in `trigonometry:ex:flatgap`.
The angle, altitude and reciprocal-altitude expressions are actual surreal functions;
their geometric identification is separate. Cubic truncations retain exact finite
fourth-order remainders.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The normalized angle series for sides `1,1,2-tau`. -/
def symmetricGapAngleSeries : PowerSeries ℝ := PowerSeries.rescale (1 / 2) acosEndpointSeries

/-- The normalized altitude series. -/
def symmetricGapHeightSeries : PowerSeries ℝ :=
  PowerSeries.rescale (-1 / 4) (PowerSeries.binomialSeries ℝ (1 / 2 : ℝ))

/-- The normalized reciprocal-altitude series. -/
def symmetricGapRadiusSeries : PowerSeries ℝ :=
  PowerSeries.rescale (-1 / 4) (PowerSeries.binomialSeries ℝ (-1 / 2 : ℝ))

@[simp] theorem coeff_symmetricGapAngleSeries (n : ℕ) :
    PowerSeries.coeff n symmetricGapAngleSeries =
      (Nat.centralBinom n : ℝ) / (16 ^ n * (2 * n + 1)) := by
  rw [symmetricGapAngleSeries, PowerSeries.coeff_rescale, coeff_acosEndpointSeries]
  have he : (16 : ℝ) ^ n = 2 ^ n * 8 ^ n := by rw [← mul_pow]; norm_num
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring_nf
  norm_num

@[simp] theorem coeff_symmetricGapHeightSeries (n : ℕ) :
    PowerSeries.coeff n symmetricGapHeightSeries = Ring.choose (1 / 2 : ℝ) n * (-1 / 4) ^ n := by
  rw [symmetricGapHeightSeries, PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff,
    smul_eq_mul, mul_one]
  ring

@[simp] theorem coeff_symmetricGapRadiusSeries (n : ℕ) :
    PowerSeries.coeff n symmetricGapRadiusSeries = Ring.choose (-1 / 2 : ℝ) n * (-1 / 4) ^ n := by
  rw [symmetricGapRadiusSeries, PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff,
    smul_eq_mul, mul_one]
  ring

private theorem infinitesimal_real_mul (r : ℝ) (τ : SignSequence.{u})
    (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.IsInfinitesimal (SignSequence.ofReal r * τ) :=
  SignSequence.finite_mul_infinitesimal (SignSequence.finite_ofReal r) hi

private theorem evaluation_rescale (r : ℝ) (τ : SignSequence.{u})
    (hi : SignSequence.IsInfinitesimal τ) (f : PowerSeries ℝ) :
    SignSequence.powerSeriesEvaluation τ hi (PowerSeries.rescale r f) =
      SignSequence.powerSeriesEvaluation (SignSequence.ofReal r * τ)
        (infinitesimal_real_mul r τ hi) f := by
  rw [SignSequence.powerSeriesEvaluation_eq_strongSum,
    SignSequence.powerSeriesEvaluation_eq_strongSum]
  congr 1
  funext n
  simp only [PowerSeries.coeff_rescale, map_mul, map_pow, mul_pow]
  ring

/-- The angle coefficient family is strongly summable at every actual infinitesimal gap. -/
theorem stronglySummable_symmetricGapAngle (τ : SignSequence.{u})
    (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.StronglySummable (fun n : ℕ =>
      SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (16 ^ n * (2 * n + 1))) * τ ^ n) :=
  SignSequence.stronglySummable_coeff_mul_powers τ hi _

/-- The altitude coefficient family is strongly summable. -/
theorem stronglySummable_symmetricGapHeight (τ : SignSequence.{u})
    (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.StronglySummable (fun n : ℕ =>
      SignSequence.ofReal (Ring.choose (1 / 2 : ℝ) n * (-1 / 4) ^ n) * τ ^ n) :=
  SignSequence.stronglySummable_coeff_mul_powers τ hi _

/-- The reciprocal-altitude coefficient family is strongly summable. -/
theorem stronglySummable_symmetricGapRadius (τ : SignSequence.{u})
    (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.StronglySummable (fun n : ℕ =>
      SignSequence.ofReal (Ring.choose (-1 / 2 : ℝ) n * (-1 / 4) ^ n) * τ ^ n) :=
  SignSequence.stronglySummable_coeff_mul_powers τ hi _

/-- The normalized angle is exact evaluation of the rescaled endpoint series. -/
theorem symmetricGap_angle_eq_powerSeries (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    (2 * arccosFunction (1 - τ / 2)) / (2 * SignSequence.sqrt τ) =
      SignSequence.powerSeriesEvaluation τ hi symmetricGapAngleSeries := by
  have he : SignSequence.ofReal (1 / 2 : ℝ) * τ = τ / 2 := by
    norm_num only [map_div₀, map_one, map_ofNat]
    ring
  have hh : SignSequence.IsInfinitesimal (τ / 2) :=
    he ▸ infinitesimal_real_mul (1 / 2) τ hi
  have hev : SignSequence.powerSeriesEvaluation τ hi symmetricGapAngleSeries =
      SignSequence.powerSeriesEvaluation (τ / 2) hh acosEndpointSeries := by
    simpa only [symmetricGapAngleSeries, he] using evaluation_rescale (1 / 2) τ hi acosEndpointSeries
  rw [hev, arccosFunction_one_sub_eq_powerSeries (τ / 2) (div_pos hp (by norm_num)) hh,
    show 2 * (τ / 2) = τ by ring]
  field_simp [(SignSequence.sqrt_pos hp).ne']

private theorem symmetricGap_height_factor (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.sqrt (τ - τ ^ 2 / 4) = SignSequence.sqrt τ *
      SignSequence.binomialPower (SignSequence.ofReal (-1 / 4 : ℝ) * τ)
        (infinitesimal_real_mul (-1 / 4) τ hi) (1 / 2 : ℝ) := by
  apply SignSequence.sqrt_eq_of_nonneg_sq
    (mul_nonneg (SignSequence.sqrt_nonneg _) (SignSequence.binomialPower_pos _ _ _).le)
  rw [mul_pow, SignSequence.sqrt_sq hp.le, SignSequence.binomialPower_half_sq]
  norm_num only [map_div₀, map_neg, map_one, map_ofNat]
  ring

/-- The normalized altitude is exact evaluation of its binomial series. -/
theorem symmetricGap_height_eq_powerSeries (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.sqrt (τ - τ ^ 2 / 4) / SignSequence.sqrt τ =
      SignSequence.powerSeriesEvaluation τ hi symmetricGapHeightSeries := by
  rw [symmetricGap_height_factor τ hp hi,
    mul_div_cancel_left₀ _ (SignSequence.sqrt_pos hp).ne',
    symmetricGapHeightSeries, evaluation_rescale]
  rfl

/-- The normalized reciprocal altitude is exact evaluation of the inverse binomial series. -/
theorem symmetricGap_radius_eq_powerSeries (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    (1 / (2 * SignSequence.sqrt (τ - τ ^ 2 / 4))) * (2 * SignSequence.sqrt τ) =
      SignSequence.powerSeriesEvaluation τ hi symmetricGapRadiusSeries := by
  rw [symmetricGap_height_factor τ hp hi, symmetricGapRadiusSeries, evaluation_rescale]
  change _ = SignSequence.binomialPower _ _ (-1 / 2 : ℝ)
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, SignSequence.binomialPower_neg]
  field_simp [(SignSequence.sqrt_pos hp).ne', SignSequence.binomialPower_ne_zero]

/-- The complete literal strong series for the normalized symmetric-gap angle. -/
theorem symmetricGap_angle_eq_strongSum (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    (2 * arccosFunction (1 - τ / 2)) / (2 * SignSequence.sqrt τ) =
      SignSequence.strongSum (fun n : ℕ =>
        SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (16 ^ n * (2 * n + 1))) * τ ^ n)
        (stronglySummable_symmetricGapAngle τ hi) := by
  rw [symmetricGap_angle_eq_powerSeries τ hp hi, SignSequence.powerSeriesEvaluation_eq_strongSum]
  simp only [coeff_symmetricGapAngleSeries]

/-- The complete literal strong series for the normalized symmetric-gap altitude. -/
theorem symmetricGap_height_eq_strongSum (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.sqrt (τ - τ ^ 2 / 4) / SignSequence.sqrt τ =
      SignSequence.strongSum (fun n : ℕ =>
        SignSequence.ofReal (Ring.choose (1 / 2 : ℝ) n * (-1 / 4) ^ n) * τ ^ n)
        (stronglySummable_symmetricGapHeight τ hi) := by
  rw [symmetricGap_height_eq_powerSeries τ hp hi, SignSequence.powerSeriesEvaluation_eq_strongSum]
  simp only [coeff_symmetricGapHeightSeries]

/-- The complete literal strong series for the normalized symmetric-gap circumradius. -/
theorem symmetricGap_radius_eq_strongSum (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    (1 / (2 * SignSequence.sqrt (τ - τ ^ 2 / 4))) * (2 * SignSequence.sqrt τ) =
      SignSequence.strongSum (fun n : ℕ =>
        SignSequence.ofReal (Ring.choose (-1 / 2 : ℝ) n * (-1 / 4) ^ n) * τ ^ n)
        (stronglySummable_symmetricGapRadius τ hi) := by
  rw [symmetricGap_radius_eq_powerSeries τ hp hi, SignSequence.powerSeriesEvaluation_eq_strongSum]
  simp only [coeff_symmetricGapRadiusSeries]

/-- The normalized angle's cubic truncation has a finite fourth-order remainder. -/
theorem symmetricGap_angle_expansion (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧ SignSequence.standardPart E = 35 / 294912 ∧
      (2 * arccosFunction (1 - τ / 2)) / (2 * SignSequence.sqrt τ) =
        1 + τ / 24 + 3 * τ ^ 2 / 640 + 5 * τ ^ 3 / 7168 + τ ^ 4 * E := by
  obtain ⟨E, hE, he, hval⟩ := SignSequence.exists_finite_powerSeries_remainder τ hi
    symmetricGapAngleSeries 4
  norm_num [coeff_symmetricGapAngleSeries, Finset.sum_range_succ,
    Nat.centralBinom, Nat.choose_succ_succ, map_div₀, map_ofNat] at he hval
  refine ⟨E, hE, he, ?_⟩
  rw [symmetricGap_angle_eq_powerSeries τ hp hi, hval]
  ring

private theorem smeval_two (r : ℝ) : Polynomial.smeval (2 : Polynomial ℤ) r = 2 := by
  simpa using Polynomial.smeval_natCast ℤ r 2

private theorem smeval_three (r : ℝ) : Polynomial.smeval (3 : Polynomial ℤ) r = 3 := by
  simpa using Polynomial.smeval_natCast ℤ r 3

/-- The normalized altitude has the literal cubic expansion and a finite fourth-order tail. -/
theorem symmetricGap_height_expansion (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧ SignSequence.standardPart E = -5 / 32768 ∧
      SignSequence.sqrt (τ - τ ^ 2 / 4) / SignSequence.sqrt τ =
        1 - τ / 8 - τ ^ 2 / 128 - τ ^ 3 / 1024 + τ ^ 4 * E := by
  obtain ⟨E, hE, he, hval⟩ := SignSequence.exists_finite_powerSeries_remainder τ hi
    symmetricGapHeightSeries 4
  norm_num [coeff_symmetricGapHeightSeries, Ring.choose_eq_smul,
    descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_one, Polynomial.smeval_natCast,
    smeval_two, smeval_three, Finset.sum_range_succ, map_div₀, map_neg, map_ofNat] at he hval
  refine ⟨E, hE, by simpa only [neg_div] using he, ?_⟩
  rw [symmetricGap_height_eq_powerSeries τ hp hi]
  linear_combination hval

/-- The normalized circumradius has the literal cubic expansion and a finite fourth-order tail. -/
theorem symmetricGap_radius_expansion (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧ SignSequence.standardPart E = 35 / 32768 ∧
      (1 / (2 * SignSequence.sqrt (τ - τ ^ 2 / 4))) * (2 * SignSequence.sqrt τ) =
        1 + τ / 8 + 3 * τ ^ 2 / 128 + 5 * τ ^ 3 / 1024 + τ ^ 4 * E := by
  obtain ⟨E, hE, he, hval⟩ := SignSequence.exists_finite_powerSeries_remainder τ hi
    symmetricGapRadiusSeries 4
  norm_num [coeff_symmetricGapRadiusSeries, Ring.choose_eq_smul,
    descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_one, Polynomial.smeval_natCast,
    smeval_two, smeval_three, Finset.sum_range_succ, map_div₀, map_neg, map_ofNat] at he hval
  refine ⟨E, hE, he, ?_⟩
  rw [symmetricGap_radius_eq_powerSeries τ hp hi]
  linear_combination hval

private theorem infinitesimal_evaluation_sub_one (τ : SignSequence.{u})
    (hi : SignSequence.IsInfinitesimal τ) (f : PowerSeries ℝ) (hf : f.coeff 0 = 1) :
    SignSequence.IsInfinitesimal (SignSequence.powerSeriesEvaluation τ hi f - 1) := by
  apply SignSequence.infinitesimal_sub_one_iff.mpr
  refine ⟨SignSequence.isFinite_powerSeriesEvaluation τ hi f, ?_⟩
  rw [SignSequence.standardPart_powerSeriesEvaluation,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]

/-- The angle is relatively equivalent to twice the square root of the gap. -/
theorem infinitesimal_symmetricGap_angle_sub_one (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.IsInfinitesimal
      ((2 * arccosFunction (1 - τ / 2)) / (2 * SignSequence.sqrt τ) - 1) := by
  rw [symmetricGap_angle_eq_powerSeries τ hp hi]
  exact infinitesimal_evaluation_sub_one τ hi _ (by norm_num)

/-- The altitude is relatively equivalent to the square root of the gap. -/
theorem infinitesimal_symmetricGap_height_sub_one (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.IsInfinitesimal
      (SignSequence.sqrt (τ - τ ^ 2 / 4) / SignSequence.sqrt τ - 1) := by
  rw [symmetricGap_height_eq_powerSeries τ hp hi]
  exact infinitesimal_evaluation_sub_one τ hi _ (by norm_num)

/-- The circumradius is relatively equivalent to one over twice the square root of the gap. -/
theorem infinitesimal_symmetricGap_radius_sub_one (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.IsInfinitesimal
      ((1 / (2 * SignSequence.sqrt (τ - τ ^ 2 / 4))) * (2 * SignSequence.sqrt τ) - 1) := by
  rw [symmetricGap_radius_eq_powerSeries τ hp hi]
  exact infinitesimal_evaluation_sub_one τ hi _ (by norm_num)

end
end Surreal.Surcomplex

import GowersSzemeredi.Proofs16CubicScalarWidth
import GowersSzemeredi.Proofs16CubicSampleBudget

/-! Apply the scalar estimate to the spectrum, sampling, and slice counts
of the constructed two-dimensional cover. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_cubic_width_lower_bound {theta gamma sigma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    let U := multipleS theta gamma 1
    let R := section16Lemma9R (theta / 2) gamma 1
    let u := (multipleC (sigma / (2 * R)) gamma 2)^R
    u^5 * sigma^10 * (2 : Real)^(-(84 * U^2 + 75)) / U^14 ≤
      section16CubicTwoAlgebraicExponent
        (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma (4 * sigma) := by
  let U := multipleS theta gamma 1
  let R := section16Lemma9R (theta / 2) gamma 1
  let u := (multipleC (sigma / (2 * R)) gamma 2)^R
  let Q := section16CubicSpectrumCount (theta / 2) gamma
  let q := section16BaseFamilyBound gamma (theta / 4)
  let M := section16UniformSampleCount sigma (theta / 2) gamma 1
  have hU : 0 < U := by dsimp [U]; unfold multipleS; positivity
  have hR1 : 1 ≤ R := by
    have hh := (section16_face_parameter_lift_reserve 1
      (by positivity : 0 < theta / 2) (by linarith : theta / 2 ≤ 1) hg hg1).1
    dsimp [R]
    norm_num [section16Lemma9R] at hh ⊢
    linarith
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hC : 0 < multipleC (sigma / (2 * R)) gamma 2 :=
    multipleC_pos 2 (by positivity) hg
  have hC1 : multipleC (sigma / (2 * R)) gamma 2 ≤ 1 := by
    unfold multipleC
    apply pow_le_one₀ (by positivity)
    have hsmall : sigma / (2 * R) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    exact mul_le_one₀ hg1 (by positivity) hsmall
  have hu : 0 < u := Real.rpow_pos_of_pos hC R
  have hu1 : u ≤ 1 := Real.rpow_le_one hC.le hC1 hR.le
  have hQi : section16Lemma9QBound sigma (theta / 2) gamma 1 = u⁻¹ := by
    simp only [section16Lemma9QBound, multipleQ, Real.inv_rpow hC.le, u, R]
  have hM : (0 : Real) < M := by
    exact_mod_cast section16UniformSampleCount_pos (theta := theta / 2) (gamma := gamma) 1 hs
  have hMs : (M : Real) ≤ 7 / (sigma * u) := by
    have hh := section16UniformSampleCount_le_seven (theta := theta / 2) (gamma := gamma)
      (k := 1) hs hs1 (by rw [hQi]; exact (one_le_inv₀ hu).mpr hu1)
    rw [hQi] at hh
    convert hh using 1; ring
  have hQ : (0 : Real) < Q := by exact_mod_cast section16CubicSpectrumCount_pos (theta / 2) gamma
  have hq : (0 : Real) < q := by exact_mod_cast section16BaseFamilyBound_pos gamma (theta / 4)
  have hV : 0 < multipleS (theta / 2) gamma 1 := by unfold multipleS; positivity
  have hscalar := section16_cubic_scalar_width hU hu hs hV hQ hM hq
    (section16RecurrenceExponent_pos_le_one 1 (3 * Q)).1.le
    (multipleS_half_le_square 1 ht ht1 hg hg1)
    (section16_cubic_spectrum_scale_le ht ht1 hg hg1)
    (section16_cubic_slice_scale_le ht ht1 hg hg1) hMs
  have hrec : (2 : Real)^(-(84 * U^2)) ≤ section16RecurrenceExponent 1 (3 * Q) := by
    rw [section16_cubic_recurrence_eq]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hh := section16_cubic_spectrum_scale_le ht ht1 hg hg1
    change (Q : Real) ≤ U^2 at hh
    linarith only [hh]
  change u^5 * sigma^10 * (2 : Real)^(-(84 * U^2 + 75)) / U^14 ≤ _
  have hproduct : (2 : Real)^(-(84 * U^2 + 75)) =
      (2 : Real)^(-(75 : Real)) * (2 : Real)^(-(84 * U^2)) := by
    rw [← Real.rpow_add (by norm_num : (0 : Real) < 2)]
    congr 1
    ring
  calc
    _ ≤ (2 : Real)^(-(75 : Real)) * u^5 * sigma^10 *
        section16RecurrenceExponent 1 (3 * Q) / U^14 := by
      rw [hproduct]
      have hc0 : 0 ≤ (2 : Real)^(-(75 : Real)) := by positivity
      have hh := mul_le_mul_of_nonneg_left hrec
        (mul_nonneg (mul_nonneg hc0
          (pow_nonneg hu.le 5)) (pow_nonneg hs.le 10))
      apply div_le_div_of_nonneg_right _ (by positivity)
      convert hh using 1; ring
    _ ≤ _ := by
      convert hscalar using 1
      simp only [section16CubicTwoAlgebraicExponent,
        show 4 * sigma / 4 = sigma by ring, section16CubicLiftExponent,
        lemma9WidthWithExponent, cubicBaseExponent, Nat.ceil_natCast]
      simp only [Nat.cast_mul]
      rfl

end LeanProofs.GowersSzemeredi

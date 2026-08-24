import FabiusFunction.FabiusLogScale
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Defect of the proposed logarithmic main term

This module isolates the explicit main term proposed in the asymptotic note and checks it
against the exact logarithmic difference equation.  It does not assume the note's formal
periodic-remainder ansatz.

The quadratic Taylor calculation leaves a residual of order
`((Real.log t) / t) ^ 2`.  In particular, this records the logarithm-squared term omitted
when the source strengthens its intermediate error estimate.
-/

set_option autoImplicit false

open Filter Asymptotics
open scoped Topology

namespace Fabius

lemma real_log_second_order_isBigO :
    (fun x : ℝ => Real.log (1 + x) - x + x ^ 2 / 2) =O[𝓝 0]
      (fun x : ℝ => x ^ 3) := by
  rw [isBigO_iff]
  refine ⟨2, ?_⟩
  filter_upwards [Metric.eventually_nhds_iff.mpr ⟨(1 / 2 : ℝ), by norm_num, fun y hy => hy⟩]
      with x hx
  rw [Real.dist_eq] at hx
  have hxhalf : |x| < 1 / 2 := by simpa using hx
  have hcx : ‖(x : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hxhalf.trans (by norm_num : (1 / 2 : ℝ) < 1)
  have hc := Complex.norm_log_sub_logTaylor_le 2 (z := (x : ℂ)) hcx
  have hone : 0 < 1 + x := by linarith [neg_lt_of_abs_lt hxhalf]
  rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_log hone.le] at hc
  norm_num [Complex.logTaylor_succ, Complex.logTaylor_zero] at hc
  have heq :
      ((Real.log (1 + x) - x + x ^ 2 / 2 : ℝ) : ℂ) =
        (Real.log (1 + x) : ℂ) - ((x : ℂ) + -(x : ℂ) ^ 2 / 2) := by
    push_cast
    ring
  rw [← heq, Complex.norm_real, Real.norm_eq_abs] at hc
  have hc' : |Real.log (1 + x) - x + x ^ 2 / 2| ≤
      |x| ^ 3 * (1 - |x|)⁻¹ / 3 := by
    exact hc
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    |Real.log (1 + x) - x + x ^ 2 / 2| ≤
        |x| ^ 3 * (1 - |x|)⁻¹ / 3 := hc'
    _ ≤ 2 * |x ^ 3| := by
      rw [abs_pow]
      have hden : (1 - |x|)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith [abs_nonneg x]) (by norm_num : (0 : ℝ) < 2)]
        linarith
      nlinarith [pow_nonneg (abs_nonneg x) 3]

lemma real_log_first_order_isBigO :
    (fun x : ℝ => Real.log (1 + x) - x) =O[𝓝 0] (fun x : ℝ => x ^ 2) := by
  have hcubic : (fun x : ℝ => x ^ 3) =O[𝓝 0] (fun x : ℝ => x ^ 2) :=
    (isLittleO_pow_pow (by omega : 2 < 3)).isBigO
  have hremainder := real_log_second_order_isBigO.trans hcubic
  have hquadratic : (fun x : ℝ => x ^ 2 / 2) =O[𝓝 0] (fun x : ℝ => x ^ 2) := by
    exact ((isBigO_refl (fun x : ℝ => x ^ 2) (𝓝 0)).const_mul_left (2 : ℝ)⁻¹).congr'
      (Filter.Eventually.of_forall fun x => by ring) (EventuallyEq.rfl)
  exact (hremainder.sub hquadratic).congr'
    (Filter.Eventually.of_forall fun x => by ring) (EventuallyEq.rfl)

/-- The explicit part of the profile proposed in equation (8) of the source. -/
noncomputable def logMainTerm (t : ℝ) : ℝ :=
  Real.log 2 / 2 * t ^ 2 + t * Real.log t -
    (1 + Real.log 2 / 2) * t + (Real.log t) ^ 2 / (2 * Real.log 2)

/-- The elementary derivative of `logMainTerm`. -/
noncomputable def logMainDerivative (t : ℝ) : ℝ :=
  Real.log 2 * t + Real.log t - Real.log 2 / 2 +
    Real.log t / (Real.log 2 * t)

/-- The derivative formula for the explicit main term away from zero. -/
theorem logMainTerm_hasDerivAt {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt logMainTerm (logMainDerivative t) t := by
  have hlog := Real.hasDerivAt_log ht
  have hlogsq := hlog.pow 2
  have hraw := (((hasDerivAt_id t).pow 2).const_mul (Real.log 2 / 2)).add
      ((hasDerivAt_id t).mul hlog) |>.sub
        ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_const t (Real.log 2 / 2)) |>.mul
          (hasDerivAt_id t)) |>.add
            (hlogsq.div_const (2 * Real.log 2))
  change HasDerivAt logMainTerm _ t at hraw
  apply hraw.congr_deriv
  unfold logMainDerivative
  norm_num [id_eq]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)]
  ring

/-- The small relative perturbation in `logMainDerivative = (log 2)t(1+u)`. -/
noncomputable def logMainDerivativePerturbation (t : ℝ) : ℝ :=
  (Real.log t - Real.log 2 / 2 + Real.log t / (Real.log 2 * t)) /
    (Real.log 2 * t)

/-- The logarithmic shift `log(1 - 1/t)` used in the finite difference. -/
noncomputable def logMainShift (t : ℝ) : ℝ :=
  Real.log (1 - 1 / t)

/-- The exact residual obtained by substituting `logMainTerm` into equation (1). -/
noncomputable def logMainDefect (t : ℝ) : ℝ :=
  (Real.log (logMainDerivative t) - Real.log (Real.log 2) -
      (1 - t) * Real.log 2) -
    (logMainTerm t - logMainTerm (t - 1))

lemma logMainDerivative_factor {t : ℝ} (ht : t ≠ 0) :
    logMainDerivative t = Real.log 2 * t * (1 + logMainDerivativePerturbation t) := by
  unfold logMainDerivative logMainDerivativePerturbation
  field_simp [ht, Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)]
  ring

/-- An exact expression for the main-term defect before Taylor estimation. -/
theorem logMainDefect_eq {t : ℝ} (ht : 1 < t) :
    logMainDefect t =
      1 + Real.log (1 + logMainDerivativePerturbation t) +
        (t - 1) * logMainShift t +
        Real.log t * logMainShift t / Real.log 2 +
        (logMainShift t) ^ 2 / (2 * Real.log 2) := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have htm10 : t - 1 ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  have ha0 : Real.log (2 : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have honeSub : 1 - 1 / t ≠ 0 := by
    rw [sub_ne_zero]
    exact ne_of_gt (by simpa using one_div_lt_one_div_of_lt zero_lt_one ht)
  have hlogShift : Real.log (t - 1) = Real.log t + logMainShift t := by
    have hfactor : t - 1 = t * (1 - 1 / t) := by field_simp
    rw [hfactor, Real.log_mul ht0 honeSub, logMainShift]
  have hpertPos : 0 < 1 + logMainDerivativePerturbation t := by
    have hderivPos : 0 < logMainDerivative t := by
      unfold logMainDerivative
      have hlogt : 0 < Real.log t := Real.log_pos ht
      have halog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have : 0 < Real.log t / (Real.log 2 * t) := div_pos hlogt (mul_pos halog (lt_trans zero_lt_one ht))
      nlinarith
    rw [logMainDerivative_factor ht0] at hderivPos
    exact pos_of_mul_pos_right hderivPos
      (mul_pos (Real.log_pos (by norm_num)) (lt_trans zero_lt_one ht)).le
  have hlogDeriv :
      Real.log (logMainDerivative t) = Real.log (Real.log 2) + Real.log t +
        Real.log (1 + logMainDerivativePerturbation t) := by
    rw [logMainDerivative_factor ht0,
      Real.log_mul (mul_ne_zero ha0 ht0) hpertPos.ne', Real.log_mul ha0 ht0]
  unfold logMainDefect logMainTerm
  rw [hlogDeriv, hlogShift]
  field_simp [ha0]
  ring

lemma tendsto_neg_one_div_atTop :
    Tendsto (fun t : ℝ => -(1 / t)) atTop (𝓝 0) := by
  simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).neg

lemma tendsto_logMainDerivativePerturbation :
    Tendsto logMainDerivativePerturbation atTop (𝓝 0) := by
  have ha0 : Real.log (2 : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hinv : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hlogdiv : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hmain : Tendsto
      (fun t : ℝ =>
        (Real.log 2)⁻¹ * (Real.log t / t) - (2 : ℝ)⁻¹ * (1 / t) +
          (Real.log 2)⁻¹ ^ 2 * (Real.log t / t) * (1 / t))
      atTop (𝓝 0) := by
    convert ((tendsto_const_nhds.mul hlogdiv).sub
      (tendsto_const_nhds.mul hinv)).add
        ((tendsto_const_nhds.mul hlogdiv).mul hinv) using 1
    all_goals norm_num
  apply hmain.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  unfold logMainDerivativePerturbation
  field_simp [ha0, ht]

lemma logMainShift_second_order_isBigO :
    (fun t : ℝ => logMainShift t + 1 / t + (1 / t) ^ 2 / 2) =O[atTop]
      (fun t : ℝ => (1 / t) ^ 3) := by
  have hcomp := real_log_second_order_isBigO.comp_tendsto tendsto_neg_one_div_atTop
  have hneg :
      (fun t : ℝ => logMainShift t + 1 / t + (1 / t) ^ 2 / 2) =O[atTop]
        (fun t : ℝ => -(1 / t) ^ 3) := hcomp.congr'
    (Filter.Eventually.of_forall fun t => by
      simp only [Function.comp_apply, logMainShift, one_div, sub_eq_add_neg]
      ring)
    (Filter.Eventually.of_forall fun t => by
      simp only [Function.comp_apply, one_div]
      ring)
  exact hneg.trans ((isBigO_refl (fun t : ℝ => (1 / t) ^ 3) atTop).neg_left)

lemma logMainDerivative_log_second_order_isBigO :
    (fun t : ℝ => Real.log (1 + logMainDerivativePerturbation t) -
      logMainDerivativePerturbation t + (logMainDerivativePerturbation t) ^ 2 / 2) =O[atTop]
      (fun t : ℝ => (logMainDerivativePerturbation t) ^ 3) := by
  exact real_log_second_order_isBigO.comp_tendsto tendsto_logMainDerivativePerturbation

noncomputable def logScaleRate (t : ℝ) : ℝ :=
  Real.log t / t

noncomputable def logScaleSquaredRate (t : ℝ) : ℝ :=
  (logScaleRate t) ^ 2

lemma tendsto_logScaleRate : Tendsto logScaleRate atTop (𝓝 0) := by
  exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

lemma one_div_isBigO_logScaleRate :
    (fun t : ℝ => 1 / t) =O[atTop] logScaleRate := by
  have h := (Real.isLittleO_const_log_atTop (c := (1 : ℝ))).isBigO.mul
    (isBigO_refl (fun t : ℝ => 1 / t) atTop)
  exact h.congr'
    (Filter.Eventually.of_forall fun t => by simp)
    (Filter.Eventually.of_forall fun t => by simp [logScaleRate, div_eq_mul_inv])

lemma one_div_isBigO_one :
    (fun t : ℝ => 1 / t) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  have h : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))
  exact h.isBigO_one ℝ

lemma logScaleRate_isBigO_one :
    logScaleRate =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
  tendsto_logScaleRate.isBigO_one ℝ

lemma logMainDerivativePerturbation_isBigO :
    logMainDerivativePerturbation =O[atTop] logScaleRate := by
  have ha0 : Real.log (2 : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hfirst : (fun t : ℝ => (Real.log 2)⁻¹ * logScaleRate t) =O[atTop]
      logScaleRate := (isBigO_refl logScaleRate atTop).const_mul_left _
  have hsecond : (fun t : ℝ => -(2 : ℝ)⁻¹ * (1 / t)) =O[atTop]
      logScaleRate := one_div_isBigO_logScaleRate.const_mul_left _
  have hthird :
      (fun t : ℝ => (Real.log 2)⁻¹ ^ 2 * logScaleRate t * (1 / t)) =O[atTop]
        logScaleRate := by
    have hmul := (isBigO_refl logScaleRate atTop).mul one_div_isBigO_one
    exact (hmul.const_mul_left ((Real.log 2)⁻¹ ^ 2)).congr'
      (Filter.Eventually.of_forall fun t => by ring)
      (Filter.Eventually.of_forall fun t => by simp)
  have hsum := (hfirst.add hsecond).add hthird
  apply hsum.congr'
  · filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    unfold logMainDerivativePerturbation logScaleRate
    field_simp [ha0, ht]
    ring
  · exact EventuallyEq.rfl

lemma logMainShift_isBigO :
    logMainShift =O[atTop] (fun t : ℝ => 1 / t) := by
  have hfirst := real_log_first_order_isBigO.comp_tendsto tendsto_neg_one_div_atTop
  have hsq : (fun t : ℝ => (-(1 / t)) ^ 2) =O[atTop] (fun t : ℝ => 1 / t) := by
    have hmul := (isBigO_refl (fun t : ℝ => 1 / t) atTop).mul one_div_isBigO_one
    exact hmul.congr'
      (Filter.Eventually.of_forall fun t => by ring)
      (Filter.Eventually.of_forall fun t => by ring)
  have hrem :
      (fun t : ℝ => logMainShift t - (-(1 / t))) =O[atTop] (fun t : ℝ => 1 / t) :=
    (hfirst.congr'
      (Filter.Eventually.of_forall fun t => by
        simp only [Function.comp_apply, logMainShift, one_div, sub_eq_add_neg])
      (EventuallyEq.rfl)).trans hsq
  have hlead : (fun t : ℝ => -(1 / t)) =O[atTop] (fun t : ℝ => 1 / t) :=
    (isBigO_refl (fun t : ℝ => 1 / t) atTop).neg_left
  exact (hrem.add hlead).congr'
    (Filter.Eventually.of_forall fun t => by ring) (EventuallyEq.rfl)

/-- The cubic Taylor remainder in the logarithm of the main-term derivative. -/
noncomputable def logMainDerivativeLogRemainder (t : ℝ) : ℝ :=
  Real.log (1 + logMainDerivativePerturbation t) - logMainDerivativePerturbation t +
    (logMainDerivativePerturbation t) ^ 2 / 2

/-- The cubic Taylor remainder in the logarithmic unit shift. -/
noncomputable def logMainShiftRemainder (t : ℝ) : ℝ :=
  logMainShift t + 1 / t + (1 / t) ^ 2 / 2

lemma logMainDerivativePerturbation_eq {t : ℝ} (ht : t ≠ 0) :
    logMainDerivativePerturbation t =
      (Real.log 2)⁻¹ * logScaleRate t - (2 : ℝ)⁻¹ * (1 / t) +
        (Real.log 2)⁻¹ ^ 2 * logScaleRate t * (1 / t) := by
  have ha0 : Real.log (2 : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  unfold logMainDerivativePerturbation logScaleRate
  field_simp [ha0, ht]

/-- Exact cancellation after both logarithms are split into quadratic Taylor parts. -/
theorem logMainDefect_decomposition {t : ℝ} (ht : 1 < t) :
    logMainDefect t =
      logMainDerivativeLogRemainder t +
        (t - 1 + Real.log t / Real.log 2) * logMainShiftRemainder t +
        (logMainShift t) ^ 2 / (2 * Real.log 2) +
        (1 / t) ^ 2 / 2 +
        ((Real.log 2)⁻¹ ^ 2 - (2 * Real.log 2)⁻¹) *
          logScaleRate t * (1 / t) -
        (logMainDerivativePerturbation t) ^ 2 / 2 := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have ha0 : Real.log (2 : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  rw [logMainDefect_eq ht]
  unfold logMainDerivativeLogRemainder logMainShiftRemainder
  rw [logMainDerivativePerturbation_eq ht0]
  unfold logScaleRate
  field_simp [ha0, ht0]
  ring

lemma one_div_sq_isBigO_logScaleSquaredRate :
    (fun t : ℝ => (1 / t) ^ 2) =O[atTop] logScaleSquaredRate := by
  exact (one_div_isBigO_logScaleRate.pow 2).congr'
    EventuallyEq.rfl
    (Filter.Eventually.of_forall fun t => by rfl)

lemma logScaleRate_cube_isBigO_logScaleSquaredRate :
    (fun t : ℝ => (logScaleRate t) ^ 3) =O[atTop] logScaleSquaredRate := by
  have hmul := ((isBigO_refl logScaleRate atTop).pow 2).mul logScaleRate_isBigO_one
  exact hmul.congr'
    (Filter.Eventually.of_forall fun t => by ring)
    (Filter.Eventually.of_forall fun t => by simp [logScaleSquaredRate])

lemma logMainDerivativeLogRemainder_isBigO :
    logMainDerivativeLogRemainder =O[atTop] logScaleSquaredRate := by
  have hcubic := logMainDerivative_log_second_order_isBigO.trans
    (logMainDerivativePerturbation_isBigO.pow 3)
  exact (hcubic.trans logScaleRate_cube_isBigO_logScaleSquaredRate).congr'
    (Filter.Eventually.of_forall fun t => by rfl)
    EventuallyEq.rfl

lemma logMainShiftRemainder_isBigO :
    logMainShiftRemainder =O[atTop] (fun t : ℝ => (1 / t) ^ 3) := by
  exact logMainShift_second_order_isBigO.congr'
    (Filter.Eventually.of_forall fun t => by rfl)
    EventuallyEq.rfl

lemma logMainDefectMultiplier_isBigO :
    (fun t : ℝ => t - 1 + Real.log t / Real.log 2) =O[atTop] (fun t : ℝ => t) := by
  have hlin := isBigO_refl (fun t : ℝ => t) atTop
  have hconst : (fun _ : ℝ => (-1 : ℝ)) =O[atTop] (fun t : ℝ => t) :=
    (isLittleO_const_id_atTop (-1 : ℝ)).isBigO
  have hlog : (fun t : ℝ => Real.log t / Real.log 2) =O[atTop] (fun t : ℝ => t) := by
    exact (Real.isLittleO_log_id_atTop.isBigO.const_mul_left (Real.log 2)⁻¹).congr'
      (Filter.Eventually.of_forall fun t => by simp [div_eq_mul_inv, mul_comm])
      EventuallyEq.rfl
  exact ((hlin.add hconst).add hlog).congr'
    (Filter.Eventually.of_forall fun t => by ring)
    EventuallyEq.rfl

lemma logMainDefectMultiplier_mul_shiftRemainder_isBigO :
    (fun t : ℝ =>
      (t - 1 + Real.log t / Real.log 2) * logMainShiftRemainder t) =O[atTop]
        logScaleSquaredRate := by
  have hprod := logMainDefectMultiplier_isBigO.mul logMainShiftRemainder_isBigO
  have hsq :
      (fun t : ℝ =>
        (t - 1 + Real.log t / Real.log 2) * logMainShiftRemainder t) =O[atTop]
          (fun t : ℝ => (1 / t) ^ 2) := by
    apply hprod.congr'
    · exact EventuallyEq.rfl
    · filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
      field_simp [ht]
  exact hsq.trans one_div_sq_isBigO_logScaleSquaredRate

lemma logMainShift_sq_div_isBigO :
    (fun t : ℝ => (logMainShift t) ^ 2 / (2 * Real.log 2)) =O[atTop]
      logScaleSquaredRate := by
  have hsq := (logMainShift_isBigO.pow 2).trans one_div_sq_isBigO_logScaleSquaredRate
  exact (hsq.const_mul_left (2 * Real.log 2)⁻¹).congr'
    (Filter.Eventually.of_forall fun t => by ring)
    EventuallyEq.rfl

lemma one_div_sq_div_two_isBigO :
    (fun t : ℝ => (1 / t) ^ 2 / 2) =O[atTop] logScaleSquaredRate := by
  exact (one_div_sq_isBigO_logScaleSquaredRate.const_mul_left (2 : ℝ)⁻¹).congr'
    (Filter.Eventually.of_forall fun t => by ring)
    EventuallyEq.rfl

lemma logMainDefect_crossTerm_isBigO :
    (fun t : ℝ =>
      ((Real.log 2)⁻¹ ^ 2 - (2 * Real.log 2)⁻¹) * logScaleRate t * (1 / t))
        =O[atTop] logScaleSquaredRate := by
  have hprod := (isBigO_refl logScaleRate atTop).mul one_div_isBigO_logScaleRate
  have hsq : (fun t : ℝ => logScaleRate t * (1 / t)) =O[atTop]
      logScaleSquaredRate := hprod.congr'
    EventuallyEq.rfl
    (Filter.Eventually.of_forall fun t => by simp [logScaleSquaredRate, pow_two])
  exact (hsq.const_mul_left
    ((Real.log 2)⁻¹ ^ 2 - (2 * Real.log 2)⁻¹)).congr'
      (Filter.Eventually.of_forall fun t => by ring)
      EventuallyEq.rfl

lemma logMainDerivativePerturbation_sq_div_two_isBigO :
    (fun t : ℝ => (logMainDerivativePerturbation t) ^ 2 / 2) =O[atTop]
      logScaleSquaredRate := by
  have hsq := logMainDerivativePerturbation_isBigO.pow 2
  exact (hsq.const_mul_left (2 : ℝ)⁻¹).congr'
    (Filter.Eventually.of_forall fun t => by ring)
    (Filter.Eventually.of_forall fun t => by rfl)

/-- The displayed main term in the source solves its exact difference equation only up to
an error of order `(log t / t)^2`.  This is the coarse bound supported by the quadratic
Taylor expansion; the source's stronger intermediate remainder estimate drops a
`(log t)^2 / t^2` contribution. -/
theorem logMainDefect_isBigO_logScaleSquaredRate :
    logMainDefect =O[atTop] logScaleSquaredRate := by
  have hsum := ((((logMainDerivativeLogRemainder_isBigO.add
      logMainDefectMultiplier_mul_shiftRemainder_isBigO).add
        logMainShift_sq_div_isBigO).add one_div_sq_div_two_isBigO).add
          logMainDefect_crossTerm_isBigO).sub
            logMainDerivativePerturbation_sq_div_two_isBigO
  apply hsum.congr'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    rw [logMainDefect_decomposition ht]
  · exact EventuallyEq.rfl

end Fabius


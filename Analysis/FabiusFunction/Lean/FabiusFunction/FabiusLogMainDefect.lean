import FabiusFunction.FabiusLogScale
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Defect of the proposed logarithmic main term

This module isolates the explicit main term proposed in the asymptotic note and checks it
against the exact logarithmic difference equation.  It does not assume the note's formal
periodic-remainder ansatz.

The quadratic Taylor calculation leaves a residual of order
`((Real.log t) / t) ^ 2`.  In particular, this records the logarithm-squared term omitted
when the source strengthens its intermediate error estimate.  The exact
remainder identity is recorded all the way down to its natural boundary
`t = 1`; the later logarithmic Taylor decomposition still uses `1 < t`.
-/

set_option autoImplicit false

open Filter Asymptotics
open scoped Topology

namespace Fabius

/-- Second-order Taylor bound for the logarithm near zero: after subtracting
`x - x ^ 2 / 2` from `Real.log (1 + x)`, the error is `O(x ^ 3)` on the
neighborhood filter `𝓝 0`.  Composing this with a function tending to zero is
how every quadratic expansion in this file is produced. -/
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

/-- First-order Taylor bound for the logarithm near zero: `Real.log (1 + x) - x`
is `O(x ^ 2)` on `𝓝 0`.  Weakened from the cubic bound above and used for the
crude estimate `logMainShift_isBigO`. -/
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

/-- The derivative of the proposed main term is positive on its full
logarithmic-scale range `1 ≤ t`, including the endpoint. -/
theorem logMainDerivative_pos {t : ℝ} (ht : 1 ≤ t) :
    0 < logMainDerivative t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have halog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hfrac : 0 ≤ Real.log t / (Real.log 2 * t) :=
    div_nonneg hlogt (mul_nonneg halog.le ht0.le)
  have hlead := mul_le_mul_of_nonneg_left ht halog.le
  simp only [mul_one] at hlead
  unfold logMainDerivative
  nlinarith

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

/-- Boundary-strengthened form of `fabiusLogRemainder_difference_eq`.  The
exact algebraic remainder identity only needs `1 ≤ t`; strict inequality is
required later when `log (t - 1)` is split into positive factors.  For the
actual remainder `g - G`, its finite difference is the difference of the two
logarithmic derivatives plus the explicitly defined defect of `G`. -/
theorem fabiusLogRemainder_difference_eq_of_one_le
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ} (ht : 1 ≤ t) :
    ((fabiusLogProfile F t - logMainTerm t) -
        (fabiusLogProfile F (t - 1) - logMainTerm (t - 1))) =
      Real.log (deriv (fabiusLogProfile F) t) -
        Real.log (deriv logMainTerm t) + logMainDefect t := by
  have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans_le ht)
  rw [(logMainTerm_hasDerivAt ht0).deriv]
  rw [show
      (fabiusLogProfile F t - logMainTerm t) -
          (fabiusLogProfile F (t - 1) - logMainTerm (t - 1)) =
        (fabiusLogProfile F t - fabiusLogProfile F (t - 1)) -
          (logMainTerm t - logMainTerm (t - 1)) by ring]
  rw [fabiusLogProfile_difference_eq_log_deriv F hF ht]
  unfold logMainDefect
  ring

/-- Exact repaired form of equation (9) on the source's strict range.  This
compatibility statement is a specialization of the boundary-strengthened
theorem `fabiusLogRemainder_difference_eq_of_one_le`. -/
theorem fabiusLogRemainder_difference_eq
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ} (ht : 1 < t) :
    ((fabiusLogProfile F t - logMainTerm t) -
        (fabiusLogProfile F (t - 1) - logMainTerm (t - 1))) =
      Real.log (deriv (fabiusLogProfile F) t) -
        Real.log (deriv logMainTerm t) + logMainDefect t :=
  fabiusLogRemainder_difference_eq_of_one_le F hF ht.le

/-- For `t ≠ 0` the derivative factors as `(log 2) * t` times
`1 + logMainDerivativePerturbation t`.  This is what lets `Real.log` of the
derivative split into `log (log 2) + log t + log (1 + u)` in
`logMainDefect_eq`. -/
lemma logMainDerivative_factor {t : ℝ} (ht : t ≠ 0) :
    logMainDerivative t = Real.log 2 * t * (1 + logMainDerivativePerturbation t) := by
  unfold logMainDerivative logMainDerivativePerturbation
  field_simp [ht, Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)]
  ring

/-- The perturbative factor in
`logMainDerivative = (log 2) * t * (1 + u)` is positive for `1 ≤ t`. -/
theorem one_add_logMainDerivativePerturbation_pos
    {t : ℝ} (ht : 1 ≤ t) :
    0 < 1 + logMainDerivativePerturbation t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hderiv := logMainDerivative_pos ht
  rw [logMainDerivative_factor ht0.ne'] at hderiv
  exact pos_of_mul_pos_right hderiv
    (mul_pos (Real.log_pos (by norm_num)) ht0).le

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
  have hpertPos : 0 < 1 + logMainDerivativePerturbation t :=
    one_add_logMainDerivativePerturbation_pos ht.le
  have hlogDeriv :
      Real.log (logMainDerivative t) = Real.log (Real.log 2) + Real.log t +
        Real.log (1 + logMainDerivativePerturbation t) := by
    rw [logMainDerivative_factor ht0,
      Real.log_mul (mul_ne_zero ha0 ht0) hpertPos.ne', Real.log_mul ha0 ht0]
  unfold logMainDefect logMainTerm
  rw [hlogDeriv, hlogShift]
  field_simp [ha0]
  ring

/-- `-(1 / t)` tends to zero as `t → ∞`.  This is the argument fed to the Taylor
bounds above to expand `logMainShift t = Real.log (1 - 1 / t)`. -/
lemma tendsto_neg_one_div_atTop :
    Tendsto (fun t : ℝ => -(1 / t)) atTop (𝓝 0) := by
  simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).neg

/-- The relative perturbation tends to zero as `t → ∞`, so the Taylor bounds
above apply to `log (1 + logMainDerivativePerturbation t)`. -/
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

/-- Quadratic expansion of the logarithmic unit shift: the residual
`logMainShift t + 1 / t + (1 / t) ^ 2 / 2` is `O((1 / t) ^ 3)` as `t → ∞`. -/
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

/-- Quadratic expansion of the logarithm of the derivative factor: writing `u`
for `logMainDerivativePerturbation t`, the residual
`log (1 + u) - u + u ^ 2 / 2` is `O(u ^ 3)` as `t → ∞`. -/
lemma logMainDerivative_log_second_order_isBigO :
    (fun t : ℝ => Real.log (1 + logMainDerivativePerturbation t) -
      logMainDerivativePerturbation t + (logMainDerivativePerturbation t) ^ 2 / 2) =O[atTop]
      (fun t : ℝ => (logMainDerivativePerturbation t) ^ 3) := by
  exact real_log_second_order_isBigO.comp_tendsto tendsto_logMainDerivativePerturbation

/-- The rate `log t / t`.  Its square is the comparison function against which
the defect of the proposed main term is measured. -/
noncomputable def logScaleRate (t : ℝ) : ℝ :=
  Real.log t / t

/-- The rate `(log t / t) ^ 2`, the comparison function in
`logMainDefect_isBigO_logScaleSquaredRate` and in the refutation of the
source's `O(t⁻²)` claim. -/
noncomputable def logScaleSquaredRate (t : ℝ) : ℝ :=
  (logScaleRate t) ^ 2

/-- `log t / t` tends to zero as `t → ∞`. -/
lemma tendsto_logScaleRate : Tendsto logScaleRate atTop (𝓝 0) := by
  exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

/-- `1 / t` is `O(log t / t)` as `t → ∞`, because the constant `1` is
eventually dominated by `log t`. -/
lemma one_div_isBigO_logScaleRate :
    (fun t : ℝ => 1 / t) =O[atTop] logScaleRate := by
  have h := (Real.isLittleO_const_log_atTop (c := (1 : ℝ))).isBigO.mul
    (isBigO_refl (fun t : ℝ => 1 / t) atTop)
  exact h.congr'
    (Filter.Eventually.of_forall fun t => by simp)
    (Filter.Eventually.of_forall fun t => by simp [logScaleRate, div_eq_mul_inv])

/-- `1 / t` is `O(1)` as `t → ∞`. -/
lemma one_div_isBigO_one :
    (fun t : ℝ => 1 / t) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  have h : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))
  exact h.isBigO_one ℝ

/-- `log t / t` is `O(1)` as `t → ∞`. -/
lemma logScaleRate_isBigO_one :
    logScaleRate =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
  tendsto_logScaleRate.isBigO_one ℝ

/-- The relative perturbation in the derivative is `O(log t / t)`.  This is the
estimate that converts the Taylor remainders into powers of `logScaleRate`. -/
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

/-- The logarithmic unit shift `log (1 - 1 / t)` is `O(1 / t)` as `t → ∞`. -/
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

/-- Exact expansion of the relative perturbation for `t ≠ 0` into the three
terms `(log 2)⁻¹ * logScaleRate t`, `-(1 / 2) * (1 / t)` and
`(log 2)⁻¹ ^ 2 * logScaleRate t * (1 / t)`.  It is an identity rather than an
estimate, and it exhibits `(log 2)⁻¹ * logScaleRate t` as the leading term. -/
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

/-- `(1 / t) ^ 2` is `O((log t / t) ^ 2)` as `t → ∞`. -/
lemma one_div_sq_isBigO_logScaleSquaredRate :
    (fun t : ℝ => (1 / t) ^ 2) =O[atTop] logScaleSquaredRate := by
  exact (one_div_isBigO_logScaleRate.pow 2).congr'
    EventuallyEq.rfl
    (Filter.Eventually.of_forall fun t => by rfl)

/-- `(log t / t) ^ 3` is `O((log t / t) ^ 2)` as `t → ∞`. -/
lemma logScaleRate_cube_isBigO_logScaleSquaredRate :
    (fun t : ℝ => (logScaleRate t) ^ 3) =O[atTop] logScaleSquaredRate := by
  have hmul := ((isBigO_refl logScaleRate atTop).pow 2).mul logScaleRate_isBigO_one
  exact hmul.congr'
    (Filter.Eventually.of_forall fun t => by ring)
    (Filter.Eventually.of_forall fun t => by simp [logScaleSquaredRate])

/-- First term of `logMainDefect_decomposition`: the cubic Taylor remainder in
`log (1 + u)` is `O((log t / t) ^ 2)`. -/
lemma logMainDerivativeLogRemainder_isBigO :
    logMainDerivativeLogRemainder =O[atTop] logScaleSquaredRate := by
  have hcubic := logMainDerivative_log_second_order_isBigO.trans
    (logMainDerivativePerturbation_isBigO.pow 3)
  exact (hcubic.trans logScaleRate_cube_isBigO_logScaleSquaredRate).congr'
    (Filter.Eventually.of_forall fun t => by rfl)
    EventuallyEq.rfl

/-- The cubic Taylor remainder in the unit shift is `O((1 / t) ^ 3)`, restated
from `logMainShift_second_order_isBigO` for the named remainder. -/
lemma logMainShiftRemainder_isBigO :
    logMainShiftRemainder =O[atTop] (fun t : ℝ => (1 / t) ^ 3) := by
  exact logMainShift_second_order_isBigO.congr'
    (Filter.Eventually.of_forall fun t => by rfl)
    EventuallyEq.rfl

/-- The multiplier `t - 1 + log t / log 2` of the shift remainder in
`logMainDefect_decomposition` is `O(t)` as `t → ∞`. -/
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

/-- Second term of `logMainDefect_decomposition`: the multiplier times the shift
remainder is `O((log t / t) ^ 2)`, being an `O(t)` times an `O((1 / t) ^ 3)`. -/
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

/-- Third term of `logMainDefect_decomposition`:
`(logMainShift t) ^ 2 / (2 * log 2)` is `O((log t / t) ^ 2)`. -/
lemma logMainShift_sq_div_isBigO :
    (fun t : ℝ => (logMainShift t) ^ 2 / (2 * Real.log 2)) =O[atTop]
      logScaleSquaredRate := by
  have hsq := (logMainShift_isBigO.pow 2).trans one_div_sq_isBigO_logScaleSquaredRate
  exact (hsq.const_mul_left (2 * Real.log 2)⁻¹).congr'
    (Filter.Eventually.of_forall fun t => by ring)
    EventuallyEq.rfl

/-- Fourth term of `logMainDefect_decomposition`: `(1 / t) ^ 2 / 2` is
`O((log t / t) ^ 2)`. -/
lemma one_div_sq_div_two_isBigO :
    (fun t : ℝ => (1 / t) ^ 2 / 2) =O[atTop] logScaleSquaredRate := by
  exact (one_div_sq_isBigO_logScaleSquaredRate.const_mul_left (2 : ℝ)⁻¹).congr'
    (Filter.Eventually.of_forall fun t => by ring)
    EventuallyEq.rfl

/-- Fifth term of `logMainDefect_decomposition`: the cross term, a constant
multiple of `logScaleRate t * (1 / t)`, is `O((log t / t) ^ 2)`. -/
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

/-- Sixth term of `logMainDefect_decomposition`: `u ^ 2 / 2` is
`O((log t / t) ^ 2)`, where `u` is `logMainDerivativePerturbation t`. -/
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

/-- `1 / t` is `o(log t / t)` as `t → ∞`.  The little-o strengthening of
`one_div_isBigO_logScaleRate`, needed for the leading-coefficient argument. -/
lemma one_div_isLittleO_logScaleRate :
    (fun t : ℝ => 1 / t) =o[atTop] logScaleRate := by
  have h := (Real.isLittleO_const_log_atTop (c := (1 : ℝ))).mul_isBigO
    (isBigO_refl (fun t : ℝ => 1 / t) atTop)
  exact h.congr'
    (Filter.Eventually.of_forall fun t => by simp)
    (Filter.Eventually.of_forall fun t => by simp [logScaleRate, div_eq_mul_inv])

/-- `(1 / t) ^ 2` is `o((log t / t) ^ 2)` as `t → ∞`. -/
lemma one_div_sq_isLittleO_logScaleSquaredRate :
    (fun t : ℝ => (1 / t) ^ 2) =o[atTop] logScaleSquaredRate := by
  exact (one_div_isLittleO_logScaleRate.pow (by omega : 0 < 2)).congr'
    EventuallyEq.rfl
    (Filter.Eventually.of_forall fun t => by rfl)

/-- `log t / t` is `o(1)` as `t → ∞`. -/
lemma logScaleRate_isLittleO_one :
    logScaleRate =o[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  rw [isLittleO_const_iff (one_ne_zero : (1 : ℝ) ≠ 0)]
  exact tendsto_logScaleRate

/-- `(log t / t) ^ 3` is `o((log t / t) ^ 2)` as `t → ∞`. -/
lemma logScaleRate_cube_isLittleO_logScaleSquaredRate :
    (fun t : ℝ => (logScaleRate t) ^ 3) =o[atTop] logScaleSquaredRate := by
  have h := ((isBigO_refl logScaleRate atTop).pow 2).mul_isLittleO
    logScaleRate_isLittleO_one
  exact h.congr'
    (Filter.Eventually.of_forall fun t => by ring)
    (Filter.Eventually.of_forall fun t => by simp [logScaleSquaredRate])

/-- Little-o form of `logMainDerivativeLogRemainder_isBigO`: the first of the
five terms of `logMainDefect_decomposition` that are negligible against
`(log t / t) ^ 2` in `logMainDefect_sub_lead_isLittleO`. -/
lemma logMainDerivativeLogRemainder_isLittleO :
    logMainDerivativeLogRemainder =o[atTop] logScaleSquaredRate := by
  have hcubic := logMainDerivative_log_second_order_isBigO.trans
    (logMainDerivativePerturbation_isBigO.pow 3)
  exact (hcubic.trans_isLittleO logScaleRate_cube_isLittleO_logScaleSquaredRate).congr'
    (Filter.Eventually.of_forall fun t => by rfl)
    EventuallyEq.rfl

/-- Little-o form of `logMainDefectMultiplier_mul_shiftRemainder_isBigO`. -/
lemma logMainDefectMultiplier_mul_shiftRemainder_isLittleO :
    (fun t : ℝ =>
      (t - 1 + Real.log t / Real.log 2) * logMainShiftRemainder t) =o[atTop]
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
  exact hsq.trans_isLittleO one_div_sq_isLittleO_logScaleSquaredRate

/-- Little-o form of `logMainShift_sq_div_isBigO`. -/
lemma logMainShift_sq_div_isLittleO :
    (fun t : ℝ => (logMainShift t) ^ 2 / (2 * Real.log 2)) =o[atTop]
      logScaleSquaredRate := by
  have hsq := (logMainShift_isBigO.pow 2).trans_isLittleO
    one_div_sq_isLittleO_logScaleSquaredRate
  exact (hsq.const_mul_left (2 * Real.log 2)⁻¹).congr'
    (Filter.Eventually.of_forall fun t => by ring)
    EventuallyEq.rfl

/-- Little-o form of `one_div_sq_div_two_isBigO`. -/
lemma one_div_sq_div_two_isLittleO :
    (fun t : ℝ => (1 / t) ^ 2 / 2) =o[atTop] logScaleSquaredRate := by
  exact (one_div_sq_isLittleO_logScaleSquaredRate.const_mul_left (2 : ℝ)⁻¹).congr'
    (Filter.Eventually.of_forall fun t => by ring)
    EventuallyEq.rfl

/-- Little-o form of `logMainDefect_crossTerm_isBigO`. -/
lemma logMainDefect_crossTerm_isLittleO :
    (fun t : ℝ =>
      ((Real.log 2)⁻¹ ^ 2 - (2 * Real.log 2)⁻¹) * logScaleRate t * (1 / t))
        =o[atTop] logScaleSquaredRate := by
  have hprod := (isBigO_refl logScaleRate atTop).mul_isLittleO
    one_div_isLittleO_logScaleRate
  have hsq : (fun t : ℝ => logScaleRate t * (1 / t)) =o[atTop]
      logScaleSquaredRate := hprod.congr'
    EventuallyEq.rfl
    (Filter.Eventually.of_forall fun t => by simp [logScaleSquaredRate, pow_two])
  exact (hsq.const_mul_left
    ((Real.log 2)⁻¹ ^ 2 - (2 * Real.log 2)⁻¹)).congr'
      (Filter.Eventually.of_forall fun t => by ring)
      EventuallyEq.rfl

/-- The relative perturbation agrees with `(log 2)⁻¹ * logScaleRate t` to higher
order: the difference is `o(log t / t)` as `t → ∞`. -/
lemma logMainDerivativePerturbation_sub_lead_isLittleO :
    (fun t : ℝ =>
      logMainDerivativePerturbation t - (Real.log 2)⁻¹ * logScaleRate t) =o[atTop]
        logScaleRate := by
  have hinvOne : (fun t : ℝ => 1 / t) =o[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    rw [isLittleO_const_iff (one_ne_zero : (1 : ℝ) ≠ 0)]
    simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hsecond := one_div_isLittleO_logScaleRate.const_mul_left (-(2 : ℝ)⁻¹)
  have hthird :
      (fun t : ℝ => (Real.log 2)⁻¹ ^ 2 * logScaleRate t * (1 / t)) =o[atTop]
        logScaleRate := by
    have hprod := (isBigO_refl logScaleRate atTop).mul_isLittleO hinvOne
    exact (hprod.const_mul_left ((Real.log 2)⁻¹ ^ 2)).congr'
      (Filter.Eventually.of_forall fun t => by ring)
      (Filter.Eventually.of_forall fun t => by simp)
  apply (hsecond.add hthird).congr'
  · filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    rw [logMainDerivativePerturbation_eq ht]
    ring
  · exact EventuallyEq.rfl

/-- Squared form of the preceding lemma: `u ^ 2` agrees with
`(log 2)⁻¹ ^ 2 * (log t / t) ^ 2` up to `o((log t / t) ^ 2)`.  This is what
supplies the nonzero leading coefficient in
`logMainDefect_sub_lead_isLittleO`. -/
lemma logMainDerivativePerturbation_sq_sub_lead_isLittleO :
    (fun t : ℝ =>
      (logMainDerivativePerturbation t) ^ 2 -
        (Real.log 2)⁻¹ ^ 2 * (logScaleRate t) ^ 2) =o[atTop]
          logScaleSquaredRate := by
  have hsum :
      (fun t : ℝ =>
        logMainDerivativePerturbation t + (Real.log 2)⁻¹ * logScaleRate t) =O[atTop]
          logScaleRate :=
    logMainDerivativePerturbation_isBigO.add
      ((isBigO_refl logScaleRate atTop).const_mul_left (Real.log 2)⁻¹)
  have hprod := logMainDerivativePerturbation_sub_lead_isLittleO.mul_isBigO hsum
  exact hprod.congr'
    (Filter.Eventually.of_forall fun t => by ring)
    (Filter.Eventually.of_forall fun t => by simp [logScaleSquaredRate, pow_two])

/-- The residual has a nonzero leading logarithm-squared coefficient. -/
theorem logMainDefect_sub_lead_isLittleO :
    (fun t : ℝ =>
      logMainDefect t - (-(2 * (Real.log 2) ^ 2)⁻¹) * logScaleSquaredRate t) =o[atTop]
        logScaleSquaredRate := by
  have hu :
      (fun t : ℝ =>
        -(logMainDerivativePerturbation t) ^ 2 / 2 -
          (-(2 * (Real.log 2) ^ 2)⁻¹) * logScaleSquaredRate t) =o[atTop]
            logScaleSquaredRate := by
    have h := logMainDerivativePerturbation_sq_sub_lead_isLittleO.const_mul_left
      (-(2 : ℝ)⁻¹)
    exact h.congr'
      (Filter.Eventually.of_forall fun t => by
        unfold logScaleSquaredRate
        ring)
      EventuallyEq.rfl
  have hsum := ((((logMainDerivativeLogRemainder_isLittleO.add
      logMainDefectMultiplier_mul_shiftRemainder_isLittleO).add
        logMainShift_sq_div_isLittleO).add one_div_sq_div_two_isLittleO).add
          logMainDefect_crossTerm_isLittleO).add hu
  apply hsum.congr'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    rw [logMainDefect_decomposition ht]
    ring
  · exact EventuallyEq.rfl

/-- The nonzero logarithm-squared leading term prevents the main defect from
being `O(t⁻²)`. -/
theorem logMainDefect_not_isBigO_one_div_sq :
    ¬ logMainDefect =O[atTop] (fun t : ℝ => (1 / t) ^ 2) := by
  intro hdefect
  have hdefectSmall : logMainDefect =o[atTop] logScaleSquaredRate :=
    hdefect.trans_isLittleO one_div_sq_isLittleO_logScaleSquaredRate
  have hleadRaw := hdefectSmall.sub logMainDefect_sub_lead_isLittleO
  let c : ℝ := -(2 * (Real.log 2) ^ 2)⁻¹
  have hlead : (fun t : ℝ => c * logScaleSquaredRate t) =o[atTop]
      logScaleSquaredRate := by
    apply hleadRaw.congr'
    · exact Filter.Eventually.of_forall fun t => by
        dsimp [c]
        ring
    · exact EventuallyEq.rfl
  have hc : c ≠ 0 := by
    dsimp [c]
    exact neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)))))
  have hself : logScaleSquaredRate =o[atTop] logScaleSquaredRate :=
    (isLittleO_const_mul_left_iff hc).mp hlead
  have hnonzero : ∀ᶠ t : ℝ in atTop, logScaleSquaredRate t ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    unfold logScaleSquaredRate logScaleRate
    exact pow_ne_zero 2
      (div_ne_zero (Real.log_pos ht).ne' (ne_of_gt (lt_trans zero_lt_one ht)))
  exact isLittleO_irrefl hnonzero.frequently hself

/-- Equation (2), first form: the second-order expansion of
`log(t - 1) - log t`, with a cubic remainder. -/
theorem log_sub_one_sub_log_second_order_isBigO :
    (fun t : ℝ => Real.log (t - 1) - Real.log t + 1 / t + (1 / t) ^ 2 / 2)
      =O[atTop] (fun t : ℝ => (1 / t) ^ 3) := by
  apply logMainShift_second_order_isBigO.congr'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
    have honeSub : 1 - 1 / t ≠ 0 := by
      rw [sub_ne_zero]
      exact ne_of_gt (by simpa using one_div_lt_one_div_of_lt zero_lt_one ht)
    have hfactor : t - 1 = t * (1 - 1 / t) := by field_simp
    rw [hfactor, Real.log_mul ht0 honeSub]
    unfold logMainShift
    ring
  · exact EventuallyEq.rfl

/-- Equation (2), reciprocal form: the expansion of `log(t / (t - 1))`. -/
theorem log_div_sub_one_second_order_isBigO :
    (fun t : ℝ => Real.log (t / (t - 1)) - 1 / t - (1 / t) ^ 2 / 2)
      =O[atTop] (fun t : ℝ => (1 / t) ^ 3) := by
  have hneg := log_sub_one_sub_log_second_order_isBigO.neg_left
  apply hneg.congr'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
    have htm10 : t - 1 ≠ 0 := ne_of_gt (sub_pos.mpr ht)
    rw [Real.log_div ht0 htm10]
    ring
  · exact EventuallyEq.rfl


end Fabius

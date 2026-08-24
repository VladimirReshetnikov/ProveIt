import FabiusFunction.FabiusLambertPhase

/-!
# Explicit lower-Lambert saddle coordinates

For a small positive argument `x`, the natural logarithmic phase in the sharp
Fabius asymptotic is the lower-Lambert solution `lambda` of

`lambda * 2 ^ (-lambda) = x`.

This module packages that phase together with the positive Laplace radius
`r = 2 ^ lambda`.  In particular, the defining equation becomes the exact
saddle-coordinate identity `r * x = lambda`.  These identities are useful for
the quantitative Bromwich argument without committing to an implicitly
defined exact saddle point.
-/

set_option autoImplicit false

namespace Fabius

/-- The explicit lower-Lambert phase for a positive Fabius argument. -/
noncomputable def fabiusLambertPhase (x : ℝ) : ℝ :=
  paperLambertN x

/-- The corresponding positive radius in the negative Laplace transform. -/
noncomputable def fabiusLambertRadius (x : ℝ) : ℝ :=
  (2 : ℝ) ^ fabiusLambertPhase x

/-- Positivity of the explicit Laplace radius. -/
theorem fabiusLambertRadius_pos (x : ℝ) :
    0 < fabiusLambertRadius x := by
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- Quotient form of the lower-Lambert saddle equation. -/
theorem fabiusLambertPhase_div_radius {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x < Real.exp (-1)) :
    fabiusLambertPhase x / fabiusLambertRadius x = x := by
  rw [fabiusLambertPhase, fabiusLambertRadius]
  have h := paperLambertN_eq9 hx hsmall
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at h
  simpa [fabiusLambertPhase, div_eq_mul_inv] using h

/-- Exact saddle-coordinate identity `r * x = lambda`. -/
theorem fabiusLambertRadius_mul_argument {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x < Real.exp (-1)) :
    fabiusLambertRadius x * x = fabiusLambertPhase x := by
  have hr := fabiusLambertRadius_pos x
  have h := fabiusLambertPhase_div_radius hx hsmall
  field_simp [hr.ne'] at h
  linarith

/-- The logarithm of the Laplace radius is `log 2` times its phase. -/
theorem log_fabiusLambertRadius (x : ℝ) :
    Real.log (fabiusLambertRadius x) =
      Real.log 2 * fabiusLambertPhase x := by
  unfold fabiusLambertRadius
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  ring

/-- On a dyadic argument, the general phase is the previously defined dyadic phase. -/
theorem fabiusLambertPhase_dyadic (t : ℝ) :
    fabiusLambertPhase ((2 : ℝ) ^ (-t)) = dyadicLambertPhase t :=
  rfl

/-- The general Laplace radius specializes to `2 ^ dyadicLambertPhase t`. -/
theorem fabiusLambertRadius_dyadic (t : ℝ) :
    fabiusLambertRadius ((2 : ℝ) ^ (-t)) =
      (2 : ℝ) ^ dyadicLambertPhase t :=
  rfl

/-- The lower-Lambert phase tends to infinity along the dyadic logarithmic scale. -/
theorem tendsto_dyadicLambertPhase_atTop :
    Filter.Tendsto dyadicLambertPhase Filter.atTop Filter.atTop := by
  have hL : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Filter.Tendsto
      (fun t : ℝ => Real.log t / Real.log 2) Filter.atTop Filter.atTop :=
    (Real.tendsto_log_atTop.atTop_mul_const (inv_pos.mpr hL)).congr'
      (Filter.Eventually.of_forall fun t => by simp [div_eq_mul_inv])
  have hmain : Filter.Tendsto
      (fun t : ℝ => t + Real.log t / Real.log 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.atTop_add_atTop hlog
  have hrem := dyadicLambertPhase_sub_main_tendsto_zero
  have hsum : Filter.Tendsto
      (fun t : ℝ =>
        (dyadicLambertPhase t - (t + Real.log t / Real.log 2)) +
          (t + Real.log t / Real.log 2)) Filter.atTop Filter.atTop :=
    hrem.add_atTop hmain
  simpa only [sub_add_cancel] using hsum

/-- The explicit dyadic Laplace radius tends to infinity. -/
theorem tendsto_fabiusLambertRadius_dyadic_atTop :
    Filter.Tendsto
      (fun t : ℝ => fabiusLambertRadius ((2 : ℝ) ^ (-t)))
      Filter.atTop Filter.atTop := by
  rw [show (fun t : ℝ => fabiusLambertRadius ((2 : ℝ) ^ (-t))) =
      fun t => (2 : ℝ) ^ dyadicLambertPhase t by
    funext t
    exact fabiusLambertRadius_dyadic t]
  have hexp : Filter.Tendsto
      (fun y : ℝ => (2 : ℝ) ^ y) Filter.atTop Filter.atTop := by
    have hL : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlin : Filter.Tendsto
        (fun y : ℝ => Real.log 2 * y) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.const_mul_atTop hL
    refine (Real.tendsto_exp_atTop.comp hlin).congr' ?_
    filter_upwards with y
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    rfl
  exact hexp.comp tendsto_dyadicLambertPhase_atTop

end Fabius

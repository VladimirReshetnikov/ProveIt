import FabiusFunction.FabiusLambertPhase

/-!
# Explicit lower-Lambert saddle coordinates

For a small positive argument `x`, the natural logarithmic phase in the sharp
Fabius asymptotic is the lower-Lambert solution `lambda` of

`lambda * 2 ^ (-lambda) = x`.

This module packages that phase together with the positive Laplace radius
`r = 2 ^ lambda`.  In particular, the defining equation becomes the exact
saddle-coordinate identity `r * x = lambda`.  On the full lower-branch domain
`(0, exp (-1) / log 2]`, the phase is strictly decreasing onto
`[1 / log 2, ∞)` and attains its lower bound exactly at the branch endpoint;
the saddle and radius identities include that endpoint.  On the open interior
the phase is continuous and has strictly negative inverse-function derivative.
These identities are useful for the quantitative Bromwich argument without
committing to an implicitly defined exact saddle point.
-/

set_option autoImplicit false

open Set Function

namespace Fabius

/-- The explicit lower-Lambert phase for a positive Fabius argument. -/
noncomputable def fabiusLambertPhase (x : ℝ) : ℝ :=
  paperLambertN x

/-- The corresponding positive radius in the negative Laplace transform. -/
noncomputable def fabiusLambertRadius (x : ℝ) : ℝ :=
  (2 : ℝ) ^ fabiusLambertPhase x

private lemma log_two_mul_le_exp_neg_one_of_mem_Ioc {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) (Real.exp (-1) / Real.log 2)) :
    Real.log 2 * x ≤ Real.exp (-1) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := (le_div_iff₀ hL).1 hx.2
  simpa only [mul_comm] using h

private lemma neg_log_two_mul_mem_lowerLambertDomain_Ico {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) (Real.exp (-1) / Real.log 2)) :
    -(Real.log 2 * x) ∈ Ico (-Real.exp (-1)) 0 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := log_two_mul_le_exp_neg_one_of_mem_Ioc hx
  exact ⟨by linarith, by nlinarith [mul_pos hL hx.1]⟩

private lemma neg_log_two_mul_mem_lowerLambertDomain {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (Real.exp (-1) / Real.log 2)) :
    -(Real.log 2 * x) ∈ Ioo (-Real.exp (-1)) 0 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall : Real.log 2 * x < Real.exp (-1) := by
    have h := (lt_div_iff₀ hL).1 hx.2
    simpa only [mul_comm] using h
  exact ⟨by linarith, by nlinarith [mul_pos hL hx.1]⟩

/-- Positivity of the explicit Laplace radius. -/
theorem fabiusLambertRadius_pos (x : ℝ) :
    0 < fabiusLambertRadius x := by
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- On the endpoint-inclusive lower-branch domain, the phase lies at or above
the turning value `1 / log 2`. -/
theorem fabiusLambertPhase_ge_inv_log_two {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) (Real.exp (-1) / Real.log 2)) :
    (Real.log 2)⁻¹ ≤ fabiusLambertPhase x := by
  simpa only [fabiusLambertPhase, one_div] using
    one_div_log_two_le_paperLambertN hx.1
      (log_two_mul_le_exp_neg_one_of_mem_Ioc hx)

/-- The lower-Lambert phase reaches its turning value exactly at the branch
endpoint `exp (-1) / log 2`. -/
theorem fabiusLambertPhase_eq_inv_log_two_iff {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) (Real.exp (-1) / Real.log 2)) :
    fabiusLambertPhase x = (Real.log 2)⁻¹ ↔
      x = Real.exp (-1) / Real.log 2 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    fabiusLambertPhase x = (Real.log 2)⁻¹ ↔
        paperLambertN x = 1 / Real.log 2 := by
          simp only [fabiusLambertPhase, one_div]
    _ ↔ Real.log 2 * x = Real.exp (-1) :=
      paperLambertN_eq_one_div_log_two_iff hx.1
        (log_two_mul_le_exp_neg_one_of_mem_Ioc hx)
    _ ↔ x = Real.exp (-1) / Real.log 2 := by
      constructor
      · intro h
        apply (eq_div_iff hL.ne').2
        simpa only [mul_comm] using h
      · intro h
        have hxmul := (eq_div_iff hL.ne').1 h
        simpa only [mul_comm] using hxmul

/-- At the lower-Lambert branch endpoint, the phase is exactly the turning
value `1 / log 2`. -/
@[simp] theorem fabiusLambertPhase_branchPoint :
    fabiusLambertPhase (Real.exp (-1) / Real.log 2) =
      (Real.log 2)⁻¹ := by
  have hx : Real.exp (-1) / Real.log 2 ∈
      Ioc (0 : ℝ) (Real.exp (-1) / Real.log 2) :=
    ⟨div_pos (Real.exp_pos _) (Real.log_pos (by norm_num)), le_rfl⟩
  exact (fabiusLambertPhase_eq_inv_log_two_iff hx).2 rfl

/-- On the natural lower-branch domain, the phase lies strictly above the
turning value `1 / log 2`. -/
theorem fabiusLambertPhase_gt_inv_log_two {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (Real.exp (-1) / Real.log 2)) :
    (Real.log 2)⁻¹ < fabiusLambertPhase x := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hW := lowerLambertW_lt_neg_one
    (neg_log_two_mul_mem_lowerLambertDomain hx)
  unfold fabiusLambertPhase paperLambertN
  have hdiv : 1 / Real.log 2 <
      -lowerLambertW (-(Real.log 2 * x)) / Real.log 2 :=
    (div_lt_div_iff_of_pos_right hL).2 (by linarith)
  simpa only [one_div] using hdiv

/-- On the full lower-branch domain, the phase lies at or beyond the turning
value `1 / log 2`. -/
theorem one_div_log_two_le_fabiusLambertPhase {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x ≤ Real.exp (-1)) :
    1 / Real.log 2 ≤ fabiusLambertPhase x := by
  simpa only [fabiusLambertPhase] using
    one_div_log_two_le_paperLambertN hx hsmall

/-- Positivity of the lower-Lambert phase on its natural argument domain. -/
theorem fabiusLambertPhase_pos_of_mem {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (Real.exp (-1) / Real.log 2)) :
    0 < fabiusLambertPhase x :=
  (inv_pos.mpr (Real.log_pos (by norm_num))).trans
    (fabiusLambertPhase_gt_inv_log_two hx)

/-- Positivity of the lower-Lambert phase on the full lower-branch domain,
including the finite branch point. -/
theorem fabiusLambertPhase_pos_of_le {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x ≤ Real.exp (-1)) :
    0 < fabiusLambertPhase x := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact lt_of_lt_of_le (one_div_pos.mpr hL)
    (one_div_log_two_le_fabiusLambertPhase hx hsmall)

/-- The derivative denominator `1 - log 2 * lambda` is strictly negative on
the lower branch, equivalently `lambda` lies beyond the turning point. -/
theorem one_sub_log_two_mul_fabiusLambertPhase_neg {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (Real.exp (-1) / Real.log 2)) :
    1 - Real.log 2 * fabiusLambertPhase x < 0 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := mul_lt_mul_of_pos_left (fabiusLambertPhase_gt_inv_log_two hx) hL
  rw [mul_inv_cancel₀ hL.ne'] at h
  linarith

/-- The lower-Lambert phase is strictly decreasing on its full
endpoint-inclusive positive argument domain. -/
theorem fabiusLambertPhase_strictAntiOn_Ioc :
    StrictAntiOn fabiusLambertPhase
      (Ioc (0 : ℝ) (Real.exp (-1) / Real.log 2)) := by
  intro x hx y hy hxy
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : -(Real.log 2 * y) < -(Real.log 2 * x) :=
    neg_lt_neg (mul_lt_mul_of_pos_left hxy hL)
  have hW := lowerLambertW_strictAntiOn_Ico
    (neg_log_two_mul_mem_lowerLambertDomain_Ico hy)
    (neg_log_two_mul_mem_lowerLambertDomain_Ico hx) harg
  unfold fabiusLambertPhase paperLambertN
  exact (div_lt_div_iff_of_pos_right hL).2 (neg_lt_neg hW)

/-- The lower-Lambert phase is strictly decreasing on its exact positive
argument domain. -/
theorem fabiusLambertPhase_strictAntiOn :
    StrictAntiOn fabiusLambertPhase
      (Ioo (0 : ℝ) (Real.exp (-1) / Real.log 2)) := by
  exact fabiusLambertPhase_strictAntiOn_Ioc.mono fun _ hx ↦
    ⟨hx.1, hx.2.le⟩

/-- Exact range of the lower-Lambert phase on its full endpoint-inclusive
positive argument domain. -/
theorem fabiusLambertPhase_image_Ioc :
    fabiusLambertPhase ''
        Ioc (0 : ℝ) (Real.exp (-1) / Real.log 2) =
      Ici (Real.log 2)⁻¹ := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact fabiusLambertPhase_ge_inv_log_two hx
  · intro y hy
    have hmul : 1 ≤ Real.log 2 * y := by
      have h := mul_le_mul_of_pos_left hy hL
      simpa only [mul_inv_cancel₀ hL.ne'] using h
    have hw : -(Real.log 2 * y) ∈ Iic (-1) := neg_le_neg hmul
    rw [← lowerLambertW_image_Ico] at hw
    obtain ⟨z, hz, hzy⟩ := hw
    let x : ℝ := -z / Real.log 2
    have hx : x ∈ Ioc (0 : ℝ) (Real.exp (-1) / Real.log 2) := by
      constructor
      · exact div_pos (neg_pos.mpr hz.2) hL
      · exact (div_le_div_iff_of_pos_right hL).2 (by linarith [hz.1])
    refine ⟨x, hx, ?_⟩
    have harg : -(Real.log 2 * x) = z := by
      dsimp [x]
      field_simp [hL.ne']
    unfold fabiusLambertPhase paperLambertN
    rw [harg, hzy]
    field_simp [hL.ne']

/-- Exact range of the lower-Lambert phase on its natural argument domain. -/
theorem fabiusLambertPhase_image :
    fabiusLambertPhase ''
        Ioo (0 : ℝ) (Real.exp (-1) / Real.log 2) =
      Ioi (Real.log 2)⁻¹ := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact fabiusLambertPhase_gt_inv_log_two hx
  · intro y hy
    have hyclosed : y ∈ Ici (Real.log 2)⁻¹ := hy.le
    rw [← fabiusLambertPhase_image_Ioc] at hyclosed
    obtain ⟨x, hx, hxy⟩ := hyclosed
    have hne : x ≠ Real.exp (-1) / Real.log 2 := by
      intro hxe
      have : (Real.log 2)⁻¹ = y := by
        simpa only [hxe, fabiusLambertPhase_branchPoint] using hxy
      exact (ne_of_lt hy) this
    exact ⟨x, ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩, hxy⟩

/-- The lower-Lambert phase is continuous at every point of its natural
argument domain. -/
theorem fabiusLambertPhase_continuousAt {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (Real.exp (-1) / Real.log 2)) :
    ContinuousAt fabiusLambertPhase x := by
  have hinner : ContinuousAt (fun y : ℝ => -(Real.log 2 * y)) x :=
    (continuousAt_const.mul continuousAt_id).neg
  have hcomp : ContinuousAt
      (fun y : ℝ => lowerLambertW (-(Real.log 2 * y))) x :=
    ContinuousAt.comp'
      (lowerLambertW_continuousAt
        (neg_log_two_mul_mem_lowerLambertDomain hx)) hinner
  apply (hcomp.neg.div_const (Real.log 2)).congr_of_eventuallyEq
  filter_upwards with y
  rfl

/-- Continuity of the lower-Lambert phase on its natural argument domain. -/
theorem fabiusLambertPhase_continuousOn :
    ContinuousOn fabiusLambertPhase
      (Ioo (0 : ℝ) (Real.exp (-1) / Real.log 2)) :=
  fun _ hx => (fabiusLambertPhase_continuousAt hx).continuousWithinAt

/-- Inverse-function derivative of the lower-Lambert phase on its natural
argument domain. -/
theorem fabiusLambertPhase_hasDerivAt {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (Real.exp (-1) / Real.log 2)) :
    HasDerivAt fabiusLambertPhase
      (Real.exp (lowerLambertW (-(Real.log 2 * x))) *
        (lowerLambertW (-(Real.log 2 * x)) + 1))⁻¹ x := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hinner : HasDerivAt (fun y : ℝ => -(Real.log 2 * y))
      (-Real.log 2) x := by
    have hraw := ((hasDerivAt_id x).const_mul (Real.log 2)).neg
    have hraw' : HasDerivAt (-fun y : ℝ => Real.log 2 * id y)
        (-Real.log 2) x := by
      simpa only [mul_one] using hraw
    apply hraw'.congr_of_eventuallyEq
    filter_upwards with y
    simp only [Pi.neg_apply, id_eq]
  have hcomp := (lowerLambertW_hasDerivAt
    (neg_log_two_mul_mem_lowerLambertDomain hx)).comp x hinner
  have hscaled := hcomp.neg.div_const (Real.log 2)
  have hderiv :
      -((Real.exp (lowerLambertW (-(Real.log 2 * x))) *
          (lowerLambertW (-(Real.log 2 * x)) + 1))⁻¹ * -Real.log 2) /
          Real.log 2 =
        (Real.exp (lowerLambertW (-(Real.log 2 * x))) *
          (lowerLambertW (-(Real.log 2 * x)) + 1))⁻¹ := by
    field_simp [hL]
  exact (hscaled.congr_deriv hderiv).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Quotient formula for the derivative, expressed entirely in saddle
coordinates.  It is the inverse derivative of
`lambda ↦ lambda * 2 ^ (-lambda)`. -/
theorem deriv_fabiusLambertPhase {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (Real.exp (-1) / Real.log 2)) :
    deriv fabiusLambertPhase x =
      fabiusLambertPhase x /
        (x * (1 - Real.log 2 * fabiusLambertPhase x)) := by
  have hz := neg_log_two_mul_mem_lowerLambertDomain hx
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hW1 : 1 + lowerLambertW (-(Real.log 2 * x)) ≠ 0 := by
    linarith [lowerLambertW_lt_neg_one hz]
  calc
    deriv fabiusLambertPhase x =
        (Real.exp (lowerLambertW (-(Real.log 2 * x))) *
          (lowerLambertW (-(Real.log 2 * x)) + 1))⁻¹ :=
      (fabiusLambertPhase_hasDerivAt hx).deriv
    _ = deriv lowerLambertW (-(Real.log 2 * x)) := by
      rw [(lowerLambertW_hasDerivAt hz).deriv]
    _ = lowerLambertW (-(Real.log 2 * x)) /
        (-(Real.log 2 * x) *
          (1 + lowerLambertW (-(Real.log 2 * x)))) :=
      deriv_lowerLambertW hz
    _ = fabiusLambertPhase x /
        (x * (1 - Real.log 2 * fabiusLambertPhase x)) := by
      unfold fabiusLambertPhase paperLambertN
      field_simp [hL, hx.1.ne', hW1]
      ring

/-- The lower-Lambert phase has strictly negative derivative throughout its
natural argument domain. -/
theorem deriv_fabiusLambertPhase_neg {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (Real.exp (-1) / Real.log 2)) :
    deriv fabiusLambertPhase x < 0 := by
  rw [deriv_fabiusLambertPhase hx]
  exact div_neg_of_pos_of_neg (fabiusLambertPhase_pos_of_mem hx)
    (mul_neg_of_pos_of_neg hx.1
      (one_sub_log_two_mul_fabiusLambertPhase_neg hx))

/-- Endpoint-inclusive quotient form of the lower-Lambert saddle equation. -/
theorem fabiusLambertPhase_div_radius_of_le {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x ≤ Real.exp (-1)) :
    fabiusLambertPhase x / fabiusLambertRadius x = x := by
  rw [fabiusLambertPhase, fabiusLambertRadius]
  have h := paperLambertN_eq9_of_le hx hsmall
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at h
  simpa [fabiusLambertPhase, div_eq_mul_inv] using h

/-- Quotient form of the lower-Lambert saddle equation on the smooth
interior. -/
theorem fabiusLambertPhase_div_radius {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x < Real.exp (-1)) :
    fabiusLambertPhase x / fabiusLambertRadius x = x :=
  fabiusLambertPhase_div_radius_of_le hx hsmall.le

/-- Endpoint-inclusive saddle-coordinate identity `r * x = lambda`. -/
theorem fabiusLambertRadius_mul_argument_of_le {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x ≤ Real.exp (-1)) :
    fabiusLambertRadius x * x = fabiusLambertPhase x := by
  have hr := fabiusLambertRadius_pos x
  have h := fabiusLambertPhase_div_radius_of_le hx hsmall
  field_simp [hr.ne'] at h
  linarith

/-- Exact saddle-coordinate identity `r * x = lambda` on the smooth
interior. -/
theorem fabiusLambertRadius_mul_argument {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x < Real.exp (-1)) :
    fabiusLambertRadius x * x = fabiusLambertPhase x :=
  fabiusLambertRadius_mul_argument_of_le hx hsmall.le

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

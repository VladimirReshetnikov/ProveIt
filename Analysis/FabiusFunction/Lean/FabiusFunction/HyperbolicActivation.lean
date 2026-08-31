import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Totalized hyperbolic activation kernels

The hyperbolic quotient `sinh x / x` is naturally equal to one at the
origin.  This module packages that removable value as `realSinhc`, proves
its basic analytic and order properties, and develops the two normalized
local kernels used by the dyadic-chaos decomposition:

* `tanhDiv x`, the totalized quotient `tanh x / x`;
* `activationOdds x`, the local variance odds;
* `activationProbability x`, the corresponding Bernoulli probability.

The algebra is organized around two denominator-free identities.  The
double-angle formula gives

`tanhDiv x * (1 + activationOdds x) = 1`,

and hence

`activationProbability x * (1 + activationOdds x) = activationOdds x`.

This order makes the value at zero automatic and postpones division until
strict positivity of the denominator is already available.

The final section proves the global elementary estimate

`activationProbability x <= x^2 / 3`.

Its proof is short but structural: first `sinh x < x cosh x` for `x > 0`,
then `tanh x < x`; differentiating
`tanh x - x + x^3/3` leaves the manifestly nonnegative quantity
`x^2 - tanh^2 x`.
-/

set_option autoImplicit false

open Set
open scoped Topology

namespace Fabius

noncomputable section

/-! ## The removable hyperbolic sinc -/

/-- The real hyperbolic sinc, totalized by its removable value one at zero. -/
noncomputable def realSinhc (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sinh x / x

/-- The hyperbolic sinc takes its removable value one at the origin. -/
@[simp] theorem realSinhc_zero : realSinhc 0 = 1 := by
  simp [realSinhc]

/-- Away from the origin, `realSinhc` is the ordinary quotient `sinh x / x`. -/
theorem realSinhc_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    realSinhc x = Real.sinh x / x := by
  simp [realSinhc, hx]

/-- The totalized hyperbolic sinc is the divided slope of `sinh` at zero. -/
theorem realSinhc_eq_dslope : realSinhc = dslope Real.sinh 0 := by
  ext x
  simp [dslope, Function.update_apply, realSinhc, slope, div_eq_inv_mul]

/-- The totalized hyperbolic sinc is continuous on the whole real line. -/
@[fun_prop] theorem continuous_realSinhc : Continuous realSinhc := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  rw [realSinhc_eq_dslope]
  by_cases hx : x = 0
  · simp [hx]
  · rw [continuousAt_dslope_of_ne hx]
    fun_prop

/-- The totalized hyperbolic sinc is even. -/
@[simp] theorem realSinhc_neg (x : ℝ) : realSinhc (-x) = realSinhc x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [realSinhc_of_ne_zero hx,
      realSinhc_of_ne_zero (neg_ne_zero.mpr hx)]

/-- `realSinhc` bundled as a `Function.Even` statement. -/
theorem realSinhc_even : Function.Even realSinhc :=
  realSinhc_neg

/-- The totalized hyperbolic sinc is strictly positive everywhere. -/
theorem realSinhc_pos (x : ℝ) : 0 < realSinhc x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [realSinhc_of_ne_zero hx.ne]
    exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hx) hx
  · simp
  · rw [realSinhc_of_ne_zero hx.ne']
    exact div_pos (Real.sinh_pos_iff.mpr hx) hx

/-- The totalized hyperbolic sinc never vanishes. -/
theorem realSinhc_ne_zero (x : ℝ) : realSinhc x ≠ 0 :=
  (realSinhc_pos x).ne'

/-- The double-angle identity for the totalized hyperbolic sinc. -/
theorem realSinhc_two_mul (x : ℝ) :
    realSinhc (2 * x) = realSinhc x * Real.cosh x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [realSinhc_of_ne_zero (mul_ne_zero (by norm_num) hx),
      realSinhc_of_ne_zero hx, Real.sinh_two_mul]
    field_simp [hx]

private lemma hasDerivAt_coshChordGap (x : ℝ) :
    HasDerivAt (id * Real.cosh - Real.sinh)
      (x * Real.sinh x) x := by
  apply (((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
    (Real.hasDerivAt_sinh x)).congr_deriv
  simp [id]

/-- For positive `x`, the chord from the origin to `(x, sinh x)` has slope
strictly below the tangent slope `cosh x`. -/
theorem sinh_lt_mul_cosh {x : ℝ} (hx : 0 < x) :
    Real.sinh x < x * Real.cosh x := by
  let g : ℝ → ℝ := id * Real.cosh - Real.sinh
  have hg (y : ℝ) : HasDerivAt g (y * Real.sinh y) y := by
    simpa [g] using hasDerivAt_coshChordGap y
  have hm : StrictMonoOn g (Ici 0) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
      (fun y _ ↦ (hg y).continuousAt.continuousWithinAt)
      (fun y _ ↦ (hg y).hasDerivWithinAt)
      (by
        intro y hy
        rw [interior_Ici, mem_Ioi] at hy
        exact mul_pos hy (Real.sinh_pos_iff.mpr hy))
  exact sub_pos.mp (by
    simpa [g] using
      hm (show 0 ∈ Ici (0 : ℝ) by simp) hx.le hx)

/-- At a positive argument, hyperbolic sinc is strictly below hyperbolic
cosine. -/
theorem realSinhc_lt_cosh_of_pos {x : ℝ} (hx : 0 < x) :
    realSinhc x < Real.cosh x := by
  rw [realSinhc_of_ne_zero hx.ne', div_lt_iff₀ hx]
  simpa [mul_comm] using sinh_lt_mul_cosh hx

/-- Hyperbolic sinc is bounded above by hyperbolic cosine on the whole real
line. -/
theorem realSinhc_le_cosh (x : ℝ) : realSinhc x ≤ Real.cosh x := by
  by_cases hx : x = 0
  · subst x
    simp
  · rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · have h := realSinhc_lt_cosh_of_pos (neg_pos.mpr hxneg)
      simpa using h.le
    · exact (realSinhc_lt_cosh_of_pos hxpos).le

/-- Hyperbolic sinc is strictly below hyperbolic cosine exactly away from
the removable point. -/
theorem realSinhc_lt_cosh_iff (x : ℝ) :
    realSinhc x < Real.cosh x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    subst x
    have : (1 : ℝ) < 1 := by
      simpa only [realSinhc_zero, Real.cosh_zero] using h
    exact (lt_irrefl 1) this
  · intro hx
    rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · have h := realSinhc_lt_cosh_of_pos (neg_pos.mpr hxneg)
      simpa using h
    · exact realSinhc_lt_cosh_of_pos hxpos

/-! ## Totalized `tanh x / x` -/

/-- The quotient `tanh x / x`, continuously totalized to one at zero. -/
noncomputable def tanhDiv (x : ℝ) : ℝ :=
  realSinhc x / Real.cosh x

/-- The totalized quotient `tanh x / x` takes the value one at zero. -/
@[simp] theorem tanhDiv_zero : tanhDiv 0 = 1 := by
  simp [tanhDiv]

/-- Away from zero, `tanhDiv` is the ordinary quotient `tanh x / x`. -/
theorem tanhDiv_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    tanhDiv x = Real.tanh x / x := by
  rw [tanhDiv, realSinhc_of_ne_zero hx,
    Real.tanh_eq_sinh_div_cosh]
  ring

/-- The totalized quotient `tanh x / x` is even. -/
@[simp] theorem tanhDiv_neg (x : ℝ) : tanhDiv (-x) = tanhDiv x := by
  simp [tanhDiv]

/-- `tanhDiv` bundled as a `Function.Even` statement. -/
theorem tanhDiv_even : Function.Even tanhDiv :=
  tanhDiv_neg

/-- The totalized quotient `tanh x / x` is continuous. -/
@[fun_prop] theorem continuous_tanhDiv : Continuous tanhDiv :=
  continuous_realSinhc.div Real.continuous_cosh
    (fun x ↦ (Real.cosh_pos x).ne')

/-- The totalized quotient `tanh x / x` is strictly positive. -/
theorem tanhDiv_pos (x : ℝ) : 0 < tanhDiv x :=
  div_pos (realSinhc_pos x) (Real.cosh_pos x)

/-- The totalized quotient `tanh x / x` never vanishes. -/
theorem tanhDiv_ne_zero (x : ℝ) : tanhDiv x ≠ 0 :=
  (tanhDiv_pos x).ne'

/-- The totalized quotient `tanh x / x` is at most one. -/
theorem tanhDiv_le_one (x : ℝ) : tanhDiv x ≤ 1 := by
  rw [tanhDiv]
  exact (div_le_one (Real.cosh_pos x)).mpr (realSinhc_le_cosh x)

/-- The totalized quotient `tanh x / x` is strictly below one exactly away
from zero. -/
theorem tanhDiv_lt_one_iff (x : ℝ) : tanhDiv x < 1 ↔ x ≠ 0 := by
  rw [tanhDiv, div_lt_one (Real.cosh_pos x), realSinhc_lt_cosh_iff]

/-- For positive `x`, the totalized quotient is at most `x⁻¹`. -/
theorem tanhDiv_le_inv_of_pos {x : ℝ} (hx : 0 < x) :
    tanhDiv x ≤ x⁻¹ := by
  have h := (div_le_div_iff_of_pos_right hx).mpr (Real.tanh_lt_one x).le
  simpa [tanhDiv_of_ne_zero hx.ne', one_div] using h

/-! ## Elementary real-tanh estimates -/

/-- The derivative of real hyperbolic tangent is `1 - tanh x ^ 2`. -/
theorem hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have htanh : Real.tanh = Real.sinh / Real.cosh := by
    funext y
    simpa only [Pi.div_apply] using
      (Real.tanh_eq_sinh_div_cosh (x := y))
  rw [htanh]
  apply ((Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (Real.cosh_pos x).ne').congr_deriv
  simp only [Pi.div_apply]
  field_simp [(Real.cosh_pos x).ne']

/-- The continuous totalization `tanhDiv` is exactly the divided slope of
hyperbolic tangent at the origin. -/
theorem tanhDiv_eq_dslope : tanhDiv = dslope Real.tanh 0 := by
  funext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [tanhDiv_zero, dslope_same]
    simpa using (hasDerivAt_tanh 0).deriv.symm
  · rw [tanhDiv_of_ne_zero hx, dslope_of_ne Real.tanh hx,
      slope_def_field]
    simp

/-- Hyperbolic tangent is nonnegative on the nonnegative half-line. -/
theorem tanh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le

/-- Hyperbolic tangent is positive at every positive argument. -/
theorem tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

/-- At every positive argument, `tanh x` is strictly below `x`. -/
theorem tanh_lt_self_of_pos {x : ℝ} (hx : 0 < x) :
    Real.tanh x < x := by
  rw [Real.tanh_eq_sinh_div_cosh,
    div_lt_iff₀ (Real.cosh_pos x)]
  simpa [mul_comm] using sinh_lt_mul_cosh hx

/-- On the nonnegative half-line, `tanh x` is bounded above by `x`. -/
theorem tanh_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.tanh x ≤ x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · exact (tanh_lt_self_of_pos hx).le

private lemma hasDerivAt_tanhCubicGap (x : ℝ) :
    HasDerivAt (Real.tanh - id + fun y : ℝ ↦ y ^ 3 / 3)
      (x ^ 2 - Real.tanh x ^ 2) x := by
  have h := ((hasDerivAt_tanh x).sub (hasDerivAt_id x)).add
    ((hasDerivAt_pow 3 x).div_const 3)
  apply h.congr_deriv
  ring

/-- The elementary cubic lower bound
`x - x^3 / 3 <= tanh x` for nonnegative `x`. -/
theorem tanh_cubic_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 3 ≤ Real.tanh x := by
  let g : ℝ → ℝ := Real.tanh - id + fun y ↦ y ^ 3 / 3
  have hg (y : ℝ) : HasDerivAt g (y ^ 2 - Real.tanh y ^ 2) y := by
    simpa [g] using hasDerivAt_tanhCubicGap y
  have hm : MonotoneOn g (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun y _ ↦ (hg y).continuousAt.continuousWithinAt)
      (fun y _ ↦ (hg y).hasDerivWithinAt)
      (by
        intro y hy
        rw [interior_Ici, mem_Ioi] at hy
        have ht0 : 0 ≤ Real.tanh y := tanh_nonneg_of_nonneg hy.le
        have hty : Real.tanh y ≤ y := (tanh_lt_self_of_pos hy).le
        exact sub_nonneg.mpr ((sq_le_sq₀ ht0 hy.le).mpr hty))
  have hgap : 0 ≤ g x := by
    simpa [g] using hm (show 0 ∈ Ici (0 : ℝ) by simp) hx hx
  have hgap' : 0 ≤ Real.tanh x - x + x ^ 3 / 3 := by
    simpa only [g, Pi.add_apply, Pi.sub_apply, id_eq] using hgap
  linarith

/-! ## Odds and activation probability -/

/-- The local activation odds obtained from the doubled hyperbolic-sinc
factor.  This definition is total at zero. -/
noncomputable def activationOdds (x : ℝ) : ℝ :=
  realSinhc (2 * x) / realSinhc x ^ 2 - 1

/-- The local activation probability, totalized by `tanhDiv 0 = 1`. -/
noncomputable def activationProbability (x : ℝ) : ℝ :=
  1 - tanhDiv x

/-- The activation odds vanish at zero. -/
@[simp] theorem activationOdds_zero : activationOdds 0 = 0 := by
  simp [activationOdds]

/-- The activation probability vanishes at zero. -/
@[simp] theorem activationProbability_zero : activationProbability 0 = 0 := by
  simp [activationProbability]

/-- Away from zero, activation probability is the report-facing quotient
`1 - tanh x / x`. -/
theorem activationProbability_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    activationProbability x = 1 - Real.tanh x / x := by
  rw [activationProbability, tanhDiv_of_ne_zero hx]

/-- The activation odds are even. -/
@[simp] theorem activationOdds_neg (x : ℝ) :
    activationOdds (-x) = activationOdds x := by
  simp [activationOdds]

/-- `activationOdds` bundled as a `Function.Even` statement. -/
theorem activationOdds_even : Function.Even activationOdds :=
  activationOdds_neg

/-- The activation probability is even. -/
@[simp] theorem activationProbability_neg (x : ℝ) :
    activationProbability (-x) = activationProbability x := by
  simp [activationProbability]

/-- `activationProbability` bundled as a `Function.Even` statement. -/
theorem activationProbability_even : Function.Even activationProbability :=
  activationProbability_neg

/-- The activation odds are continuous. -/
@[fun_prop] theorem continuous_activationOdds : Continuous activationOdds := by
  have htwo : Continuous (fun x : ℝ ↦ 2 * x) :=
    continuous_const.mul continuous_id
  exact ((continuous_realSinhc.comp htwo).div
    (continuous_realSinhc.pow 2)
    (fun x ↦ pow_ne_zero 2 (realSinhc_ne_zero x))).sub continuous_const

/-- The activation probability is continuous. -/
@[fun_prop] theorem continuous_activationProbability :
    Continuous activationProbability :=
  continuous_const.sub continuous_tanhDiv

/-- Adding one to the activation odds cancels one hyperbolic-sinc factor. -/
theorem one_add_activationOdds (x : ℝ) :
    1 + activationOdds x = Real.cosh x / realSinhc x := by
  rw [activationOdds, realSinhc_two_mul]
  field_simp [realSinhc_ne_zero x] ; ring

/-- The denominator `1 + activationOdds x` is strictly positive. -/
theorem one_add_activationOdds_pos (x : ℝ) :
    0 < 1 + activationOdds x := by
  rw [one_add_activationOdds]
  exact div_pos (Real.cosh_pos x) (realSinhc_pos x)

/-- Away from zero, the activation odds are the classical expression
`x * cosh x / sinh x - 1` (that is, `x coth x - 1` without introducing a
partial `coth`). -/
theorem activationOdds_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    activationOdds x = x * Real.cosh x / Real.sinh x - 1 := by
  have hsinh : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
  have h : 1 + activationOdds x =
      x * Real.cosh x / Real.sinh x := by
    rw [one_add_activationOdds, realSinhc_of_ne_zero hx]
    field_simp [hx, hsinh]
  linarith

/-- The activation odds are globally nonnegative. -/
theorem activationOdds_nonneg (x : ℝ) : 0 ≤ activationOdds x := by
  have hratio : 1 ≤ Real.cosh x / realSinhc x := by
    rw [le_div_iff₀ (realSinhc_pos x)]
    simpa using realSinhc_le_cosh x
  rw [← one_add_activationOdds x] at hratio
  linarith

/-- The activation odds are strictly positive exactly away from zero. -/
theorem activationOdds_pos_iff (x : ℝ) :
    0 < activationOdds x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    subst x
    have : (0 : ℝ) < 0 := by
      simpa only [activationOdds_zero] using h
    exact (lt_irrefl 0) this
  · intro hx
    have hratio : 1 < Real.cosh x / realSinhc x := by
      rw [lt_div_iff₀ (realSinhc_pos x)]
      simpa using (realSinhc_lt_cosh_iff x).mpr hx
    rw [← one_add_activationOdds x] at hratio
    linarith

/-- The complementary factor and the odds denominator cancel exactly. -/
theorem tanhDiv_mul_one_add_activationOdds (x : ℝ) :
    tanhDiv x * (1 + activationOdds x) = 1 := by
  rw [tanhDiv, one_add_activationOdds]
  field_simp [realSinhc_ne_zero x, (Real.cosh_pos x).ne']

/-- The denominator-free odds/probability identity.  This is the primary
bridge because it includes the origin without a side condition. -/
theorem activationProbability_mul_one_add_activationOdds (x : ℝ) :
    activationProbability x * (1 + activationOdds x) = activationOdds x := by
  calc
    activationProbability x * (1 + activationOdds x) =
        (1 - tanhDiv x) * (1 + activationOdds x) := rfl
    _ = 1 + activationOdds x -
        tanhDiv x * (1 + activationOdds x) := by ring
    _ = activationOdds x := by
      rw [tanhDiv_mul_one_add_activationOdds]
      ring

/-- Activation probability is odds divided by one plus odds, globally and
without a nonzero-argument hypothesis. -/
theorem activationProbability_eq_odds_div (x : ℝ) :
    activationProbability x = activationOdds x / (1 + activationOdds x) := by
  apply (eq_div_iff (one_add_activationOdds_pos x).ne').mpr
  exact activationProbability_mul_one_add_activationOdds x

/-- The complement of activation probability is exactly `tanhDiv`. -/
theorem one_sub_activationProbability (x : ℝ) :
    1 - activationProbability x = tanhDiv x := by
  rw [activationProbability]
  ring

/-- The complement of activation probability is strictly positive. -/
theorem one_sub_activationProbability_pos (x : ℝ) :
    0 < 1 - activationProbability x := by
  rw [one_sub_activationProbability]
  exact tanhDiv_pos x

/-- The complement of activation probability is at most one. -/
theorem one_sub_activationProbability_le_one (x : ℝ) :
    1 - activationProbability x ≤ 1 := by
  rw [one_sub_activationProbability]
  exact tanhDiv_le_one x

/-- At a positive argument, the complement of activation probability is at
most `x⁻¹`. -/
theorem one_sub_activationProbability_le_inv_of_pos {x : ℝ} (hx : 0 < x) :
    1 - activationProbability x ≤ x⁻¹ := by
  rw [one_sub_activationProbability]
  exact tanhDiv_le_inv_of_pos hx

/-- At a positive argument, the complement of activation probability is
bounded simultaneously by one and by `x⁻¹`. -/
theorem one_sub_activationProbability_le_min_one_inv_of_pos
    {x : ℝ} (hx : 0 < x) :
    1 - activationProbability x ≤ min 1 x⁻¹ :=
  le_min (one_sub_activationProbability_le_one x)
    (one_sub_activationProbability_le_inv_of_pos hx)

/-- The activation probability is globally nonnegative. -/
theorem activationProbability_nonneg (x : ℝ) :
    0 ≤ activationProbability x := by
  rw [activationProbability]
  exact sub_nonneg.mpr (tanhDiv_le_one x)

/-- The activation probability is strictly positive exactly away from zero. -/
theorem activationProbability_pos_iff (x : ℝ) :
    0 < activationProbability x ↔ x ≠ 0 := by
  rw [activationProbability, sub_pos, tanhDiv_lt_one_iff]

/-- The activation probability is strictly less than one everywhere. -/
theorem activationProbability_lt_one (x : ℝ) :
    activationProbability x < 1 := by
  rw [activationProbability]
  linarith [tanhDiv_pos x]

/-- On the nonnegative half-line, activation probability satisfies the
quadratic estimate `p(x) <= x^2 / 3`. -/
theorem activationProbability_le_sq_div_three_of_nonneg {x : ℝ}
    (hx : 0 ≤ x) : activationProbability x ≤ x ^ 2 / 3 := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · rw [activationProbability, tanhDiv_of_ne_zero hx.ne']
    have hdiv : 1 - x ^ 2 / 3 ≤ Real.tanh x / x := by
      rw [le_div_iff₀ hx]
      nlinarith [tanh_cubic_lower hx.le]
    linarith

/-- **Global quadratic activation bound.**  For every real argument,
`activationProbability x <= x^2 / 3`. -/
theorem activationProbability_le_sq_div_three (x : ℝ) :
    activationProbability x ≤ x ^ 2 / 3 := by
  by_cases hx : 0 ≤ x
  · exact activationProbability_le_sq_div_three_of_nonneg hx
  · have h := activationProbability_le_sq_div_three_of_nonneg
      (show 0 ≤ -x by linarith)
    simpa using h

/-- The report-facing combined activation bound, strengthened from the
nonnegative half-line to every real argument. -/
theorem activationProbability_le_min_one_sq_div_three (x : ℝ) :
    activationProbability x ≤ min 1 (x ^ 2 / 3) :=
  le_min (activationProbability_lt_one x).le
    (activationProbability_le_sq_div_three x)

end

end Fabius

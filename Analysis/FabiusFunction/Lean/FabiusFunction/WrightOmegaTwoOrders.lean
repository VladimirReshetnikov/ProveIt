import FabiusFunction.WrightOmega
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Two orders of the basic inverse

The two asymptotic clauses of the transseries volume's
`plt:prop:mot-two-orders`, for Wright's omega function `ω` of
`FabiusFunction.WrightOmega`:

`ω(X) - X ∼ -log X`,   `ω(X) - X + log X ∼ (log X)/X`.

Together they are the volume's motivating computation in miniature: the
first correction to `X` is *logarithmic*, so no expansion in powers of
`X` alone can reach it; the second correction is `(log X)/X`, a *mixed*
monomial, so no expansion in powers of `log X` alone can reach it either.
The two facts are what force both generators `t = X⁻¹` and `L = log X`
(`plt:cor:mot-both-generators-needed`).

Everything comes from the defining equation `ω + log ω = X`, which makes
the first residual exactly `-log ω(X)`; the work is transferring the
logarithm from `ω` to `X`:

* `wrightOmega_lt_self` — the envelope is strict above `1`.
* `tendsto_log_wrightOmega_div_atTop_zero`, `tendsto_wrightOmega_div_atTop_one`
  — `log ω(X)/X → 0` and hence `ω(X)/X → 1`.
* `tendsto_log_wrightOmega_sub_log_atTop_zero` — `log ω(X) - log X → 0`,
  the sharp form: the two logarithms differ by `o(1)`, not merely by
  `o(log X)`.
* `tendsto_log_wrightOmega_div_log_atTop_one` — the ratio form.
* `self_sub_wrightOmega_isEquivalent_log`,
  `wrightOmega_sub_self_isEquivalent_neg_log` — **first order**.
* `wrightOmega_residual_isEquivalent` — **second order**.  The residual is
  `-log(1 - log ω(X)/X)`, and the slope of `log` at `1` turns that into
  `log ω(X)/X`, which the previous ratio identifies with `(log X)/X`.

Not formalized here: the four-term expansion
`ω = X - L + L/X + (L²/2 - L)/X² + O(L³/X³)` and the explicit envelope
`½·L/X ≤ ω - X + L ≤ 2·L/X` for `X ≥ X₀`.  Both are quantitative
refinements of what is proved here; the asymptotic clauses are what the
volume's structural corollaries actually use.
-/

set_option autoImplicit false

open Filter Topology Asymptotics

namespace Fabius

/-- Above `1` the envelope is strict: `ω(X) < X`. -/
theorem wrightOmega_lt_self {X : ℝ} (hX : 1 < X) : wrightOmega X < X := by
  have h := wrightOmega_add_log X
  have h1 : 1 ≤ wrightOmega X := one_le_wrightOmega hX.le
  rcases eq_or_lt_of_le h1 with he | hlt
  · exfalso
    rw [← he] at h
    simp at h
    linarith
  · have hpos : 0 < Real.log (wrightOmega X) := Real.log_pos hlt
    linarith

/-- `log ω(X)/X → 0`: the correction is small relative to `X`. -/
theorem tendsto_log_wrightOmega_div_atTop_zero :
    Tendsto (fun X => Real.log (wrightOmega X) / X) atTop (𝓝 0) := by
  have hlogid : Tendsto (fun X : ℝ => Real.log X / X) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  refine squeeze_zero' ?_ ?_ hlogid
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have h1 : 1 ≤ wrightOmega X := one_le_wrightOmega hX.le
    exact div_nonneg (Real.log_nonneg h1) (by linarith)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hle : wrightOmega X ≤ X := wrightOmega_le_self hX.le
    have hpos : 0 < wrightOmega X := wrightOmega_pos X
    exact div_le_div_of_nonneg_right (Real.log_le_log hpos hle) (by linarith)

/-- `ω(X)/X → 1`. -/
theorem tendsto_wrightOmega_div_atTop_one :
    Tendsto (fun X => wrightOmega X / X) atTop (𝓝 1) := by
  have hu := tendsto_log_wrightOmega_div_atTop_zero
  have h1 : Tendsto (fun X : ℝ => 1 - Real.log (wrightOmega X) / X) atTop
      (𝓝 (1 - 0)) := tendsto_const_nhds.sub hu
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hne : X ≠ 0 := by linarith
  have h := wrightOmega_add_log X
  field_simp
  linarith

/-- **The logarithm of `ω` is the logarithm of `X`, to within `o(1)`.** -/
theorem tendsto_log_wrightOmega_sub_log_atTop_zero :
    Tendsto (fun X => Real.log (wrightOmega X) - Real.log X) atTop (𝓝 0) := by
  have hcont : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
  have hcomp := hcont.tendsto.comp tendsto_wrightOmega_div_atTop_one
  rw [Real.log_one] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hpos : 0 < wrightOmega X := wrightOmega_pos X
  show Real.log (wrightOmega X / X) = Real.log (wrightOmega X) - Real.log X
  exact Real.log_div hpos.ne' (by linarith)

/-- `log ω(X)/log X → 1`. -/
theorem tendsto_log_wrightOmega_div_log_atTop_one :
    Tendsto (fun X => Real.log (wrightOmega X) / Real.log X) atTop (𝓝 1) := by
  have hdiff := tendsto_log_wrightOmega_sub_log_atTop_zero
  have hlog : Tendsto (fun X : ℝ => Real.log X) atTop atTop := Real.tendsto_log_atTop
  have hq : Tendsto
      (fun X => (Real.log (wrightOmega X) - Real.log X) / Real.log X) atTop (𝓝 0) :=
    hdiff.div_atTop hlog
  have h1 : Tendsto
      (fun X => 1 + (Real.log (wrightOmega X) - Real.log X) / Real.log X) atTop
      (𝓝 (1 + 0)) := tendsto_const_nhds.add hq
  rw [add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hlogpos : 0 < Real.log X := Real.log_pos hX
  field_simp
  ring

/-- **First order** (`plt:prop:mot-two-orders`): `X - ω(X) ∼ log X`, i.e.
`ω(X) - X ∼ -log X`.  The defining equation makes the difference exactly
`log ω(X)`, so this is the previous lemma. -/
theorem self_sub_wrightOmega_isEquivalent_log :
    (fun X => X - wrightOmega X) ~[atTop] fun X => Real.log X := by
  have hz : ∀ᶠ X in atTop, Real.log X ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact (Real.log_pos hX).ne'
  rw [Asymptotics.isEquivalent_iff_tendsto_one hz]
  refine Tendsto.congr' ?_ tendsto_log_wrightOmega_div_log_atTop_one
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have h := wrightOmega_add_log X
  show Real.log (wrightOmega X) / Real.log X = (X - wrightOmega X) / Real.log X
  congr 1
  linarith

/-- The volume's spelling of the first order. -/
theorem wrightOmega_sub_self_isEquivalent_neg_log :
    (fun X => wrightOmega X - X) ~[atTop] fun X => -Real.log X := by
  have hz : ∀ᶠ X in atTop, -Real.log X ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact neg_ne_zero.2 (Real.log_pos hX).ne'
  rw [Asymptotics.isEquivalent_iff_tendsto_one hz]
  refine Tendsto.congr' ?_ tendsto_log_wrightOmega_div_log_atTop_one
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have h := wrightOmega_add_log X
  have hrw : wrightOmega X - X = -Real.log (wrightOmega X) := by linarith
  show Real.log (wrightOmega X) / Real.log X =
    (wrightOmega X - X) / -Real.log X
  rw [hrw, neg_div_neg_eq]

/-- The slope of `log` at `1`: `log y/(y - 1) → 1` as `y → 1`. -/
private theorem tendsto_slope_log_one :
    Tendsto (fun y : ℝ => Real.log y / (y - 1)) (𝓝[≠] (1 : ℝ)) (𝓝 1) := by
  have h : HasDerivAt Real.log (1 : ℝ)⁻¹ 1 := Real.hasDerivAt_log one_ne_zero
  rw [hasDerivAt_iff_tendsto_slope, inv_one] at h
  refine h.congr fun y => ?_
  rw [slope_def_field, Real.log_one, sub_zero]

/-- **Second order** (`plt:prop:mot-two-orders`):
`ω(X) - X + log X ∼ (log X)/X`.  Writing `A = log ω(X)`, the defining
equation gives `ω(X)/X = 1 - A/X`, so the residual is `-log(1 - A/X)`,
which the slope of `log` at `1` converts into `A/X`, and `A ∼ log X`. -/
theorem wrightOmega_residual_isEquivalent :
    (fun X => wrightOmega X - X + Real.log X) ~[atTop]
      fun X => Real.log X / X := by
  have hy : Tendsto (fun X => wrightOmega X / X) atTop (𝓝[≠] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_wrightOmega_div_atTop_one ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hlt := wrightOmega_lt_self hX
    exact ne_of_lt ((div_lt_one (by linarith)).2 hlt)
  have hcomp := tendsto_slope_log_one.comp hy
  have hmul := hcomp.mul tendsto_log_wrightOmega_div_log_atTop_one
  rw [one_mul] at hmul
  have hz : ∀ᶠ X in atTop, Real.log X / X ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact div_ne_zero (Real.log_pos hX).ne' (by linarith)
  rw [Asymptotics.isEquivalent_iff_tendsto_one hz]
  refine Tendsto.congr' ?_ hmul
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hLpos : 0 < Real.log X := Real.log_pos hX
  have hwpos : 0 < wrightOmega X := wrightOmega_pos X
  have hw1 : 1 < wrightOmega X := by
    have := wrightOmega_strictMono hX
    rw [wrightOmega_one] at this
    exact this
  have hApos : 0 < Real.log (wrightOmega X) := Real.log_pos hw1
  have heq := wrightOmega_add_log X
  have hlogdiv : Real.log (wrightOmega X / X) =
      Real.log (wrightOmega X) - Real.log X := Real.log_div hwpos.ne' hXpos.ne'
  show Real.log (wrightOmega X / X) / (wrightOmega X / X - 1) *
      (Real.log (wrightOmega X) / Real.log X) =
    (wrightOmega X - X + Real.log X) / (Real.log X / X)
  rw [hlogdiv]
  have hsub : wrightOmega X / X - 1 = -(Real.log (wrightOmega X) / X) := by
    field_simp
    linarith
  rw [hsub]
  have hnum : wrightOmega X - X + Real.log X =
      Real.log X - Real.log (wrightOmega X) := by linarith
  rw [hnum]
  field_simp
  ring

end Fabius

import FabiusFunction.PoissonApproximateIdentity
import FabiusFunction.PoissonMassSwap
import FabiusFunction.StepMeasureBridge
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Stieltjes--Perron inversion for the up-measure

`FabiusFunction.StieltjesInversion` writes the boundary profile of
the Cauchy transform of the up-measure as a Poisson average,
`π⁻¹·(-Im R(x + iε)) = ∫ π⁻¹·ε/((x-t)² + ε²) dμ_up(t)`, and
`FabiusFunction.PoissonApproximateIdentity` evaluates the Lebesgue
integrals of that kernel exactly, through the arctangent
antiderivative.  Both scope notes recorded Stieltjes--Perron
inversion as still outside the corpus.  This module proves it.

Throughout, `P_ε(t) = π⁻¹·(arctan ((b-t)/ε) - arctan ((a-t)/ε))`
is `Fabius.poissonIntervalMass`.  There are three steps.

### The exchange

For `ε > 0` and `a ≤ b`,

`∫_{(a,b)} π⁻¹·(-Im R(x + iε)) dx = ∫ P_ε(t) dμ_up(t)`.

The inner `x`-integral of the kernel is computed by the *same*
antiderivative `Fabius.hasDerivAt_arctan_poisson` that
`FabiusFunction.PoissonApproximateIdentity` uses on the two
half-lines, now run on a bounded interval; that evaluation is
`setIntegral_poisson_kernel_interval`.  The exchange itself is
Fubini on `volume.restrict (a,b) ×ˢ μ_up`, whose integrability
hypothesis is `integrable_poisson_kernel_prod_restrict`.

### The profile

`P_ε(t) < 1` holds for every `a`, `b`, `ε`, `t` whatsoever, and
`0 < P_ε(t)` whenever `a < b` and `ε > 0`, with no condition on
`t`.  Both bounds are strict, so the two limits below are
approached and never attained.  The constant `π⁻¹` is pinned by the
calibration `P_{b-a}(a) = 1/4`.

As `ε → 0⁺`: `P_ε(t) → 1` for `t ∈ (a,b)`; `P_ε(t) → 0` for `t < a`
and also for `t > b`; and at the two endpoints `P_ε(a) → 1/2` and
`P_ε(b) → 1/2`.

### The passage to the limit

`|P_ε| ≤ 1` and `μ_up` is a probability measure, so dominated
convergence applies along `ε → 0⁺`.  The classical endpoint
hypothesis `μ({a}) = μ({b}) = 0` is *automatic* here: the up-measure
has a density, hence charges no point
(`Fabius.rvachevMeasure_singleton`, imported), so the endpoint
values `1/2` sit on a `μ_up`-null set.  Therefore, for every
`a < b` and with no side condition at all,

`lim_{ε → 0⁺} π⁻¹·∫_{(a,b)} (-Im R(x + iε)) dx = μ_up((a,b))`.

For the same reason the open interval may be exchanged for the
closed one, which is recorded as `rvachevMeasure_real_Icc_eq_Ioo`.

## Main declarations

* `Fabius.poissonIntervalMass` — the interval Poisson mass `P_ε(t)`.
* `Fabius.poissonIntervalMass_def` — its defining formula.
* `Fabius.integrable_poisson_kernel_shift` — Lebesgue integrability
  of `x ↦ ε/((x-t)² + ε²)`.
* `Fabius.setIntegral_poisson_kernel_interval` — **the bounded
  interval evaluation** `∫_{(a,b)} ε/((x-t)²+ε²) dx
  = arctan ((b-t)/ε) - arctan ((a-t)/ε)`.
* `Fabius.setIntegral_poisson_density_interval` — its normalised
  form, equal to `P_ε(t)`.
* `Fabius.poissonIntervalMass_nonneg` — nonnegativity for `a ≤ b`.
* `Fabius.poissonIntervalMass_pos` — `0 < P_ε(t)` for `a < b`,
  `ε > 0`: the limit `0` is never attained.
* `Fabius.poissonIntervalMass_lt_one` — `P_ε(t) < 1`
  unconditionally: the limit `1` is never attained.
* `Fabius.abs_poissonIntervalMass_le_one` — the dominating bound.
* `Fabius.poissonIntervalMass_calibration` — `P_{b-a}(a) = 1/4`.
* `Fabius.continuous_poissonIntervalMass` — continuity in `t`.
* `Fabius.integrable_poisson_kernel_prod_restrict` — the Fubini
  integrability hypothesis on `volume.restrict (a,b) ×ˢ μ_up`.
* `Fabius.setIntegral_inv_pi_mul_neg_im_eq` — **the exchange**.
* `Fabius.tendsto_poissonIntervalMass_of_mem_Ioo` — interior limit
  `1`.
* `Fabius.tendsto_poissonIntervalMass_of_lt` and `_of_gt` — the two
  exterior limits `0`.
* `Fabius.tendsto_poissonIntervalMass_left` and `_right` — the
  endpoint limits `1/2`.
* `Fabius.rvachevMeasure_ae_tendsto_poissonIntervalMass` — the
  `μ_up`-a.e. limit, the indicator of `(a,b)`.
* `Fabius.tendsto_setIntegral_inv_pi_mul_neg_im` — **the
  Stieltjes--Perron inversion**.
* `Fabius.stieltjesPerron_inversion` — the same with the constant
  `π⁻¹` pulled outside the integral.
* `Fabius.rvachevMeasure_real_Icc_eq_Ioo` — the endpoints do not
  matter.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Real

namespace Fabius

/-! ### The interval Poisson mass -/

/-- **The interval Poisson mass**: the `π⁻¹`-normalised Poisson mass
that the height-`ε` kernel seen from `t` puts on the interval
`(a, b)`.  The name is justified by
`setIntegral_poisson_density_interval`, which identifies it with
`∫_{(a,b)} π⁻¹·ε/((x-t)² + ε²) dx`. -/
noncomputable def poissonIntervalMass (a b ε t : ℝ) : ℝ :=
  π⁻¹ * (Real.arctan ((b - t) / ε) - Real.arctan ((a - t) / ε))

/-- The defining formula of `poissonIntervalMass`. -/
theorem poissonIntervalMass_def (a b ε t : ℝ) :
    poissonIntervalMass a b ε t =
      π⁻¹ * (Real.arctan ((b - t) / ε)
        - Real.arctan ((a - t) / ε)) := rfl

private theorem poissonIntervalMass_as_fun_of_scale (a b t : ℝ) :
    (fun ε : ℝ => poissonIntervalMass a b ε t)
      = fun ε : ℝ => π⁻¹ * (Real.arctan ((b - t) / ε)
        - Real.arctan ((a - t) / ε)) := rfl

private theorem poissonIntervalMass_as_fun_of_point (a b ε : ℝ) :
    (fun t : ℝ => poissonIntervalMass a b ε t)
      = fun t : ℝ => π⁻¹ * (Real.arctan ((b - t) / ε)
        - Real.arctan ((a - t) / ε)) := rfl

/-! ### The bounded-interval evaluation -/

/-- The Poisson kernel is Lebesgue integrable in its *first*
argument.  This is `Fabius.integrable_poisson_kernel` carried across
the symmetry `Fabius.poisson_kernel_symm`. -/
theorem integrable_poisson_kernel_shift (t : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    Integrable (fun x : ℝ => ε / ((x - t) ^ 2 + ε ^ 2)) :=
  (integrable_poisson_kernel t hε).congr
    (Filter.Eventually.of_forall fun x =>
      (poisson_kernel_symm x t ε).symm)

/-- **The bounded-interval evaluation**: for `ε > 0` and `a ≤ b`,
`∫_{(a,b)} ε/((x-t)² + ε²) dx
  = arctan ((b-t)/ε) - arctan ((a-t)/ε)`.
The antiderivative is `Fabius.hasDerivAt_arctan_poisson`, reused
with its two real arguments exchanged. -/
theorem setIntegral_poisson_kernel_interval (t : ℝ) {a b ε : ℝ}
    (hab : a ≤ b) (hε : 0 < ε) :
    ∫ x in Set.Ioo a b, ε / ((x - t) ^ 2 + ε ^ 2)
      = Real.arctan ((b - t) / ε)
        - Real.arctan ((a - t) / ε) := by
  have hd : ∀ s : ℝ,
      HasDerivAt (fun u : ℝ => Real.arctan ((u - t) / ε))
        (ε / ((s - t) ^ 2 + ε ^ 2)) s := by
    intro s
    have h := hasDerivAt_arctan_poisson t hε s
    rwa [← poisson_kernel_symm s t ε] at h
  have hint : IntervalIntegrable
      (fun x : ℝ => ε / ((x - t) ^ 2 + ε ^ 2)) volume a b :=
    (integrable_poisson_kernel_shift t hε).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => Real.arctan ((u - t) / ε))
    (f' := fun s : ℝ => ε / ((s - t) ^ 2 + ε ^ 2))
    (fun s _ => hd s) hint
  rwa [intervalIntegral.integral_of_le hab,
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at hftc

/-- **The normalised interval evaluation**: for `ε > 0` and `a ≤ b`
the `π⁻¹`-normalised kernel integrates over `(a, b)` in `x` to
`poissonIntervalMass a b ε t`. -/
theorem setIntegral_poisson_density_interval (t : ℝ) {a b ε : ℝ}
    (hab : a ≤ b) (hε : 0 < ε) :
    ∫ x in Set.Ioo a b, π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2))
      = poissonIntervalMass a b ε t := by
  rw [poissonIntervalMass_def, MeasureTheory.integral_const_mul,
    setIntegral_poisson_kernel_interval t hab hε]

/-! ### Bounds on the interval mass -/

/-- The interval mass is nonnegative when `a ≤ b` and `ε > 0`. -/
theorem poissonIntervalMass_nonneg {a b : ℝ} (hab : a ≤ b) {ε : ℝ}
    (hε : 0 < ε) (t : ℝ) :
    0 ≤ poissonIntervalMass a b ε t := by
  have hle : (a - t) / ε ≤ (b - t) / ε := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith)
      (le_of_lt (inv_pos.mpr hε))
  have harc : Real.arctan ((a - t) / ε)
      ≤ Real.arctan ((b - t) / ε) := Real.arctan_mono hle
  have hπ : (0 : ℝ) ≤ π⁻¹ := le_of_lt (inv_pos.mpr Real.pi_pos)
  rw [poissonIntervalMass_def]
  exact mul_nonneg hπ (by linarith)

/-- **The interval mass never vanishes**: for `a < b` and `ε > 0`
it is strictly positive at *every* `t`, however far outside `(a,b)`.
So the exterior limit `0` of `tendsto_poissonIntervalMass_of_lt`
and `tendsto_poissonIntervalMass_of_gt` is approached and never
attained. -/
theorem poissonIntervalMass_pos {a b : ℝ} (hab : a < b) {ε : ℝ}
    (hε : 0 < ε) (t : ℝ) : 0 < poissonIntervalMass a b ε t := by
  have hlt : (a - t) / ε < (b - t) / ε := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right (by linarith) (inv_pos.mpr hε)
  have harc : Real.arctan ((a - t) / ε)
      < Real.arctan ((b - t) / ε) := Real.arctan_strictMono hlt
  have hπ : (0 : ℝ) < π⁻¹ := inv_pos.mpr Real.pi_pos
  rw [poissonIntervalMass_def]
  exact mul_pos hπ (by linarith)

/-- **The interval mass never reaches one**, with no hypothesis on
`a`, `b`, `ε` or `t`: the arctangent range `(-π/2, π/2)` bounds the
bracket strictly by `π`.  So the interior limit `1` of
`tendsto_poissonIntervalMass_of_mem_Ioo` is approached and never
attained. -/
theorem poissonIntervalMass_lt_one (a b ε t : ℝ) :
    poissonIntervalMass a b ε t < 1 := by
  have h1 : Real.arctan ((b - t) / ε) < π / 2 :=
    Real.arctan_lt_pi_div_two _
  have h2 : -(π / 2) < Real.arctan ((a - t) / ε) :=
    Real.neg_pi_div_two_lt_arctan _
  have hπ : (0 : ℝ) < π⁻¹ := inv_pos.mpr Real.pi_pos
  have hd : Real.arctan ((b - t) / ε)
      - Real.arctan ((a - t) / ε) < π := by linarith
  have h3 : π⁻¹ * (Real.arctan ((b - t) / ε)
      - Real.arctan ((a - t) / ε)) < π⁻¹ * π :=
    mul_lt_mul_of_pos_left hd hπ
  rw [inv_mul_cancel₀ Real.pi_ne_zero] at h3
  rw [poissonIntervalMass_def]
  exact h3

/-- The dominating bound used by the dominated-convergence pass:
`|P_ε(t)| ≤ 1` for `a ≤ b` and `ε > 0`. -/
theorem abs_poissonIntervalMass_le_one {a b : ℝ} (hab : a ≤ b)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    |poissonIntervalMass a b ε t| ≤ 1 := by
  have h0 := poissonIntervalMass_nonneg hab hε t
  have h1 := poissonIntervalMass_lt_one a b ε t
  rw [abs_of_nonneg h0]
  linarith

/-- **Calibration**: at the scale `ε = b - a` the left endpoint
carries mass exactly `1/4`.  This pins the constant `π⁻¹` in
`poissonIntervalMass`. -/
theorem poissonIntervalMass_calibration {a b : ℝ} (hab : a < b) :
    poissonIntervalMass a b (b - a) a = 1 / 4 := by
  have hne : b - a ≠ 0 := ne_of_gt (by linarith)
  rw [poissonIntervalMass_def, div_self hne, sub_self, zero_div,
    Real.arctan_one, Real.arctan_zero, sub_zero]
  have e : π / 4 = π * (1 / 4) := by ring
  rw [e, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]

/-- The interval mass is continuous in `t`, for every `ε`. -/
theorem continuous_poissonIntervalMass (a b ε : ℝ) :
    Continuous fun t : ℝ => poissonIntervalMass a b ε t := by
  have hlin : ∀ c : ℝ, Continuous fun t : ℝ => (c - t) / ε := by
    intro c
    exact (continuous_const.sub continuous_id').div_const ε
  have hb : Continuous fun t : ℝ => Real.arctan ((b - t) / ε) :=
    Real.continuous_arctan.comp' (hlin b)
  have ha : Continuous fun t : ℝ => Real.arctan ((a - t) / ε) :=
    Real.continuous_arctan.comp' (hlin a)
  rw [poissonIntervalMass_as_fun_of_point]
  exact continuous_const.mul (hb.sub ha)

/-! ### The Fubini exchange -/

/-- The integrability hypothesis of the Fubini exchange: on
`volume.restrict (a,b) ×ˢ μ_up` the normalised Poisson kernel is
integrable.  It is jointly measurable
(`Fabius.measurable_poisson_kernel_prod`), bounded by `π⁻¹·ε⁻¹`
(`Fabius.poisson_kernel_le_inv`), and both factors of the product
measure are finite. -/
theorem integrable_poisson_kernel_prod_restrict (F : BoundedFabius)
    (hF : IsFabius F) (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (Function.uncurry fun x t : ℝ =>
        π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)))
      ((volume.restrict (Set.Ioo a b)).prod
        (rvachevMeasure F)) := by
  haveI := rvachevMeasure_isProbability F hF
  have hmeas : Measurable (Function.uncurry fun x t : ℝ =>
      π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2))) := by
    have h : Measurable fun p : ℝ × ℝ =>
        π⁻¹ * (ε / ((p.1 - p.2) ^ 2 + ε ^ 2)) :=
      (measurable_poisson_kernel_prod hε).const_mul π⁻¹
    exact h
  have hπ : (0 : ℝ) < π⁻¹ := inv_pos.mpr Real.pi_pos
  refine Integrable.mono' (integrable_const (π⁻¹ * ε⁻¹))
    hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  have hk : 0 < ε / ((p.1 - p.2) ^ 2 + ε ^ 2) :=
    poisson_kernel_pos p.1 p.2 hε
  show ‖π⁻¹ * (ε / ((p.1 - p.2) ^ 2 + ε ^ 2))‖
      ≤ π⁻¹ * ε⁻¹
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hπ hk)]
  exact mul_le_mul_of_nonneg_left
    (poisson_kernel_le_inv p.1 p.2 hε) (le_of_lt hπ)

/-- **The Fubini exchange**: for `ε > 0` and `a ≤ b` the Lebesgue
integral of the boundary profile over `(a, b)` is the `μ_up`-average
of the interval Poisson mass,

`∫_{(a,b)} π⁻¹·(-Im R(x + iε)) dx = ∫ P_ε(t) dμ_up(t)`.

This is the substantive, `ε`-fixed half of Stieltjes--Perron
inversion. -/
theorem setIntegral_inv_pi_mul_neg_im_eq (F : BoundedFabius)
    (hF : IsFabius F) {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) :
    ∫ x in Set.Ioo a b,
        π⁻¹ * (-(rvachevCauchyTransform F
          (x + ε * Complex.I)).im)
      = ∫ t : ℝ, poissonIntervalMass a b ε t
        ∂(rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  have hstep1 : ∫ x in Set.Ioo a b,
      π⁻¹ * (-(rvachevCauchyTransform F
        (x + ε * Complex.I)).im)
      = ∫ x in Set.Ioo a b, (∫ t : ℝ,
          π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2))
            ∂(rvachevMeasure F)) :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x =>
        inv_pi_mul_neg_im_rvachevCauchyTransform_eq F hF x hε)
  have hstep2 : ∫ x in Set.Ioo a b, (∫ t : ℝ,
        π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2))
          ∂(rvachevMeasure F))
      = ∫ t : ℝ, (∫ x in Set.Ioo a b,
        π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)))
          ∂(rvachevMeasure F) :=
    MeasureTheory.integral_integral_swap
      (integrable_poisson_kernel_prod_restrict F hF a b hε)
  rw [hstep1, hstep2]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun t =>
      setIntegral_poisson_density_interval t hab hε)

/-! ### The pointwise limits as `ε → 0⁺` -/

private theorem tendsto_arctan_div_pos {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun ε : ℝ => Real.arctan (c / ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (π / 2)) := by
  have hinv : Filter.Tendsto (fun ε : ℝ => ε⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  have hdiv : Filter.Tendsto (fun ε : ℝ => c / ε)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    (Filter.Tendsto.const_mul_atTop hc hinv).congr fun ε =>
      (div_eq_mul_inv c ε).symm
  exact tendsto_nhds_of_tendsto_nhdsWithin
    (Real.tendsto_arctan_atTop.comp hdiv)

private theorem tendsto_arctan_div_neg {c : ℝ} (hc : c < 0) :
    Filter.Tendsto (fun ε : ℝ => Real.arctan (c / ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(π / 2))) := by
  have h := (tendsto_arctan_div_pos (c := -c) (by linarith)).neg
  refine h.congr fun ε => ?_
  show -Real.arctan (-c / ε) = Real.arctan (c / ε)
  rw [← Real.arctan_neg, neg_div, neg_neg]

private theorem tendsto_arctan_div_self (c : ℝ) :
    Filter.Tendsto (fun ε : ℝ => Real.arctan ((c - c) / ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have e : (fun ε : ℝ => Real.arctan ((c - c) / ε))
      = fun _ : ℝ => (0 : ℝ) := by
    funext ε
    rw [sub_self, zero_div, Real.arctan_zero]
  rw [e]
  exact tendsto_const_nhds

/-- **The interior limit**: for `t` strictly inside `(a, b)` the
interval Poisson mass tends to `1` as `ε → 0⁺`. -/
theorem tendsto_poissonIntervalMass_of_mem_Ioo {a b t : ℝ}
    (ht : t ∈ Set.Ioo a b) :
    Filter.Tendsto (fun ε : ℝ => poissonIntervalMass a b ε t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hb : 0 < b - t := by
    have h := (Set.mem_Ioo.mp ht).2
    linarith
  have ha : a - t < 0 := by
    have h := (Set.mem_Ioo.mp ht).1
    linarith
  have h : Filter.Tendsto
      (fun ε : ℝ => π⁻¹ * (Real.arctan ((b - t) / ε)
        - Real.arctan ((a - t) / ε)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (π⁻¹ * (π / 2 - -(π / 2)))) :=
    tendsto_const_nhds.mul
      ((tendsto_arctan_div_pos hb).sub (tendsto_arctan_div_neg ha))
  have hv : π⁻¹ * (π / 2 - -(π / 2)) = 1 := by
    have e : π / 2 - -(π / 2) = π := by ring
    rw [e, inv_mul_cancel₀ Real.pi_ne_zero]
  rw [hv] at h
  rw [poissonIntervalMass_as_fun_of_scale]
  exact h

/-- **The left exterior limit**: for `t < a ≤ b` the interval
Poisson mass tends to `0` as `ε → 0⁺`. -/
theorem tendsto_poissonIntervalMass_of_lt {a b t : ℝ} (hab : a ≤ b)
    (ht : t < a) :
    Filter.Tendsto (fun ε : ℝ => poissonIntervalMass a b ε t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hb : 0 < b - t := by linarith
  have ha : 0 < a - t := by linarith
  have h : Filter.Tendsto
      (fun ε : ℝ => π⁻¹ * (Real.arctan ((b - t) / ε)
        - Real.arctan ((a - t) / ε)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (π⁻¹ * (π / 2 - π / 2))) :=
    tendsto_const_nhds.mul
      ((tendsto_arctan_div_pos hb).sub (tendsto_arctan_div_pos ha))
  rw [sub_self, mul_zero] at h
  rw [poissonIntervalMass_as_fun_of_scale]
  exact h

/-- **The right exterior limit**: for `a ≤ b < t` the interval
Poisson mass tends to `0` as `ε → 0⁺`. -/
theorem tendsto_poissonIntervalMass_of_gt {a b t : ℝ} (hab : a ≤ b)
    (ht : b < t) :
    Filter.Tendsto (fun ε : ℝ => poissonIntervalMass a b ε t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hb : b - t < 0 := by linarith
  have ha : a - t < 0 := by linarith
  have h : Filter.Tendsto
      (fun ε : ℝ => π⁻¹ * (Real.arctan ((b - t) / ε)
        - Real.arctan ((a - t) / ε)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (π⁻¹ * (-(π / 2) - -(π / 2)))) :=
    tendsto_const_nhds.mul
      ((tendsto_arctan_div_neg hb).sub (tendsto_arctan_div_neg ha))
  rw [sub_self, mul_zero] at h
  rw [poissonIntervalMass_as_fun_of_scale]
  exact h

/-- **The left endpoint limit**: at `t = a` the interval Poisson
mass tends to `1/2`, halfway between the interior and the exterior
values. -/
theorem tendsto_poissonIntervalMass_left {a b : ℝ} (hab : a < b) :
    Filter.Tendsto (fun ε : ℝ => poissonIntervalMass a b ε a)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := by
  have hb : 0 < b - a := by linarith
  have h : Filter.Tendsto
      (fun ε : ℝ => π⁻¹ * (Real.arctan ((b - a) / ε)
        - Real.arctan ((a - a) / ε)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (π⁻¹ * (π / 2 - 0))) :=
    tendsto_const_nhds.mul
      ((tendsto_arctan_div_pos hb).sub (tendsto_arctan_div_self a))
  have hv : π⁻¹ * (π / 2 - 0) = 1 / 2 := by
    have e : π / 2 - 0 = π * (1 / 2) := by ring
    rw [e, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
  rw [hv] at h
  rw [poissonIntervalMass_as_fun_of_scale]
  exact h

/-- **The right endpoint limit**: at `t = b` the interval Poisson
mass tends to `1/2` as well. -/
theorem tendsto_poissonIntervalMass_right {a b : ℝ} (hab : a < b) :
    Filter.Tendsto (fun ε : ℝ => poissonIntervalMass a b ε b)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := by
  have ha : a - b < 0 := by linarith
  have h : Filter.Tendsto
      (fun ε : ℝ => π⁻¹ * (Real.arctan ((b - b) / ε)
        - Real.arctan ((a - b) / ε)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (π⁻¹ * (0 - -(π / 2)))) :=
    tendsto_const_nhds.mul
      ((tendsto_arctan_div_self b).sub (tendsto_arctan_div_neg ha))
  have hv : π⁻¹ * (0 - -(π / 2)) = 1 / 2 := by
    have e : (0 : ℝ) - -(π / 2) = π * (1 / 2) := by ring
    rw [e, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
  rw [hv] at h
  rw [poissonIntervalMass_as_fun_of_scale]
  exact h

/-! ### The `μ_up`-almost-everywhere limit -/

/-- **The a.e. limit**: for `a < b` the interval Poisson mass tends,
`μ_up`-almost everywhere, to the indicator of `(a, b)`.  The two
endpoints, where the limit is `1/2` instead
(`tendsto_poissonIntervalMass_left`,
`tendsto_poissonIntervalMass_right`), are discarded because the
up-measure charges no point.  This is where the classical endpoint
hypothesis of Stieltjes--Perron inversion is *discharged* rather
than assumed. -/
theorem rvachevMeasure_ae_tendsto_poissonIntervalMass
    (F : BoundedFabius) {a b : ℝ} (hab : a < b) :
    ∀ᵐ t ∂(rvachevMeasure F), Filter.Tendsto
      (fun ε : ℝ => poissonIntervalMass a b ε t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Set.indicator (Set.Ioo a b)
        (fun _ => (1 : ℝ)) t)) := by
  have hA : ∀ᵐ t ∂(rvachevMeasure F), t ≠ a := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
      (rvachevMeasure_singleton F a)] with t ht
    simpa using ht
  have hB : ∀ᵐ t ∂(rvachevMeasure F), t ≠ b := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
      (rvachevMeasure_singleton F b)] with t ht
    simpa using ht
  filter_upwards [hA, hB] with t hta htb
  rcases lt_trichotomy t a with h | h | h
  · have hnm : t ∉ Set.Ioo a b := fun hm =>
      absurd (Set.mem_Ioo.mp hm).1 (not_lt.mpr h.le)
    rw [Set.indicator_of_notMem hnm]
    exact tendsto_poissonIntervalMass_of_lt hab.le h
  · exact absurd h hta
  · rcases lt_trichotomy t b with h2 | h2 | h2
    · rw [Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨h, h2⟩)]
      exact tendsto_poissonIntervalMass_of_mem_Ioo
        (Set.mem_Ioo.mpr ⟨h, h2⟩)
    · exact absurd h2 htb
    · have hnm : t ∉ Set.Ioo a b := fun hm =>
        absurd (Set.mem_Ioo.mp hm).2 (not_lt.mpr h2.le)
      rw [Set.indicator_of_notMem hnm]
      exact tendsto_poissonIntervalMass_of_gt hab.le h2

/-! ### Stieltjes--Perron inversion -/

/-- **Stieltjes--Perron inversion for the up-measure**: for every
`a < b`,

`lim_{ε → 0⁺} ∫_{(a,b)} π⁻¹·(-Im R(x + iε)) dx = μ_up((a,b))`.

No hypothesis on the endpoints is needed: the up-measure has a
density, so `μ_up {a} = μ_up {b} = 0` automatically
(`Fabius.rvachevMeasure_singleton`).  The proof is the Fubini
exchange `setIntegral_inv_pi_mul_neg_im_eq` followed by dominated
convergence, dominated by the constant `1` of
`abs_poissonIntervalMass_le_one`. -/
theorem tendsto_setIntegral_inv_pi_mul_neg_im (F : BoundedFabius)
    (hF : IsFabius F) {a b : ℝ} (hab : a < b) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x in Set.Ioo a b,
        π⁻¹ * (-(rvachevCauchyTransform F
          (x + ε * Complex.I)).im))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((rvachevMeasure F).real (Set.Ioo a b))) := by
  haveI := rvachevMeasure_isProbability F hF
  have hind : ∫ t : ℝ, Set.indicator (Set.Ioo a b)
      (fun _ => (1 : ℝ)) t ∂(rvachevMeasure F)
      = (rvachevMeasure F).real (Set.Ioo a b) := by
    rw [MeasureTheory.integral_indicator_const (1 : ℝ)
      measurableSet_Ioo, smul_eq_mul, mul_one]
  have hDCT : Filter.Tendsto
      (fun ε : ℝ => ∫ t : ℝ, poissonIntervalMass a b ε t
        ∂(rvachevMeasure F))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((rvachevMeasure F).real (Set.Ioo a b))) := by
    rw [← hind]
    refine
      MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (fun _ => (1 : ℝ)) ?_ ?_ (integrable_const 1)
        (rvachevMeasure_ae_tendsto_poissonIntervalMass F hab)
    · exact Filter.Eventually.of_forall fun ε =>
        (continuous_poissonIntervalMass a b ε).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      refine Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs]
      exact abs_poissonIntervalMass_le_one hab.le hε' t
  refine hDCT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  exact (setIntegral_inv_pi_mul_neg_im_eq F hF hab.le hε').symm

/-- **Stieltjes--Perron inversion, classical form**: for every
`a < b`,

`lim_{ε → 0⁺} π⁻¹·∫_{(a,b)} (-Im R(x + iε)) dx = μ_up((a,b))`,

the normalising constant now standing outside the integral. -/
theorem stieltjesPerron_inversion (F : BoundedFabius)
    (hF : IsFabius F) {a b : ℝ} (hab : a < b) :
    Filter.Tendsto
      (fun ε : ℝ => π⁻¹ * ∫ x in Set.Ioo a b,
        -(rvachevCauchyTransform F (x + ε * Complex.I)).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((rvachevMeasure F).real (Set.Ioo a b))) := by
  refine (tendsto_setIntegral_inv_pi_mul_neg_im F hF hab).congr' ?_
  refine Filter.Eventually.of_forall fun ε => ?_
  dsimp only
  rw [MeasureTheory.integral_const_mul]

/-- **The endpoints do not matter**: the up-measure charges no
point, so the open interval of `stieltjesPerron_inversion` may be
replaced by the closed one.  This is the guard on the reading of the
inversion: no `μ({a}) = μ({b}) = 0` side condition was silently
dropped, because there is none to impose. -/
theorem rvachevMeasure_real_Icc_eq_Ioo (F : BoundedFabius)
    (a b : ℝ) :
    (rvachevMeasure F).real (Set.Icc a b)
      = (rvachevMeasure F).real (Set.Ioo a b) :=
  (measureReal_congr (MeasureTheory.Ioo_ae_eq_Icc'
    (rvachevMeasure_singleton F a)
    (rvachevMeasure_singleton F b))).symm

end Fabius

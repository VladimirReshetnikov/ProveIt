import Mathlib.Analysis.SpecificLimits.Basic
import FabiusFunction.MeasureCauchyTransform

/-!
# Moment/Laurent expansions for bounded real measures

This module gives the compact-support moment expansion for an arbitrary finite
real measure, with coefficients and spectral parameters in any real-or-complex
field `𝕜`.  The expansion may be centered at any `c : 𝕜`: if the embedded real
measure is almost everywhere contained in the closed ball of radius `R` about
`c`, then for `R < ‖z - c‖` one has

`∫ (z-x)⁻¹ dμ(x) = ∑_{k<N} m_k(c) / (z-c)^(k+1)
  + (z-c)^(-N) ∫ ((x-c)^N / (z-x)) dμ(x)`.

Here `m_k(c) = ∫ (x-c)^k dμ(x)`.  The remainder is bounded by

`μ(ℝ) * (‖z-c‖-R)⁻¹ * (R / ‖z-c‖)^N`,

so the full Laurent series is supplied in `Summable`, `tsum`, and `HasSum`
forms.  The measure need not be a probability measure, and the support
hypothesis is stated almost everywhere so that no topological support theorem
is needed.  Small wrappers identify the complex-valued direct integral with
the project's oriented `measureCauchyTransform`.

## Main results

* `inv_sub_eq_sum_range_add` is the field-generic finite geometric identity.
* `integral_inv_sub_eq_sum_range_measureCauchyMoment_add` is the exact finite
  Laurent identity with its integral remainder over every `RCLike` field.
* `norm_measureCauchyMoment_le` bounds every centered moment by the support
  radius and total mass.
* `integrable_centered_pow_div_sub_of_ae_norm_sub_le` and
  `integrable_inv_sub_of_ae_norm_sub_le` expose the reusable off-ball
  integrability estimates.
* `norm_integral_inv_sub_sub_sum_range_measureCauchyMoment_le` is the generic
  geometric finite-remainder bound.
* `summable_measureCauchyMoment_laurent`,
  `integral_inv_sub_eq_tsum_measureCauchyMoment`, and
  `hasSum_measureCauchyMoment_laurent` give convergence of the full series.
* The `measureCauchyTransform_*` theorems are complex-valued wrappers for the
  named oriented transform.
-/

set_option autoImplicit false

open MeasureTheory

namespace Fabius

/-- Finite geometric expansion of the Cauchy kernel, in any field:
`(z-x)⁻¹ = ∑_{k<N} x^k/z^{k+1} + x^N/(z^N(z-x))`. -/
theorem inv_sub_eq_sum_range_add {K : Type*} [Field K] (N : ℕ)
    {z x : K} (hz : z ≠ 0) (hzx : z - x ≠ 0) :
    (z - x)⁻¹ = (∑ k ∈ Finset.range N, x ^ k / z ^ (k + 1)) +
      x ^ N / (z ^ N * (z - x)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep : x ^ N / z ^ (N + 1) +
        x ^ (N + 1) / (z ^ (N + 1) * (z - x)) =
        x ^ N / (z ^ N * (z - x)) := by
      field_simp
      ring
    rw [Finset.sum_range_succ, add_assoc, hstep]
    exact ih

/-- The `RCLike`-valued moment of a real measure centered at `c`:
`m_n(c) = ∫ ((x : 𝕜) - c)^n dμ(x)`.

For bounded finite measures these are the Laurent coefficients of the direct
Cauchy-kernel integral, and for `𝕜 = ℂ` of `measureCauchyTransform μ`. -/
noncomputable def measureCauchyMoment
    {𝕜 : Type*} [RCLike 𝕜]
    (μ : Measure ℝ) (c : 𝕜) (n : ℕ) : 𝕜 :=
  ∫ x : ℝ, ((x : 𝕜) - c) ^ n ∂μ

/-- The zeroth centered moment is the total mass of the measure, embedded in
the chosen real-or-complex scalar field. -/
@[simp] theorem measureCauchyMoment_zero
    {𝕜 : Type*} [RCLike 𝕜]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (c : 𝕜) :
    measureCauchyMoment μ c 0 = (μ.real Set.univ : 𝕜) := by
  simp [measureCauchyMoment, Algebra.smul_def]

private theorem inv_sub_eq_sum_range_add_centered
    {K : Type*} [Field K] (N : ℕ) {z x c : K}
    (hzc : z - c ≠ 0) (hzx : z - x ≠ 0) :
    (z - x)⁻¹ =
      (∑ k ∈ Finset.range N, (x - c) ^ k / (z - c) ^ (k + 1)) +
        (x - c) ^ N / ((z - c) ^ N * (z - x)) := by
  have hdiff : (z - c) - (x - c) = z - x := by ring
  have h := inv_sub_eq_sum_range_add (K := K) N
    (z := z - c) (x := x - c) hzc (by rwa [hdiff])
  rwa [hdiff] at h

private theorem stronglyMeasurable_centered_pow
    {𝕜 : Type*} [RCLike 𝕜] (c : 𝕜) (n : ℕ) :
    StronglyMeasurable (fun x : ℝ => ((x : 𝕜) - c) ^ n) := by
  exact ((RCLike.continuous_ofReal.sub continuous_const).pow n).stronglyMeasurable

/-- The inverse Cauchy kernel is measurable over every real-or-complex scalar
field, including at real poles where it is not globally continuous. -/
theorem measurable_inv_sub_rclike
    {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) :
    Measurable (fun x : ℝ => (z - (x : 𝕜))⁻¹) := by
  exact (measurable_const.sub RCLike.continuous_ofReal.measurable).inv

private theorem stronglyMeasurable_inv_sub
    {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) :
    StronglyMeasurable (fun x : ℝ => (z - (x : 𝕜))⁻¹) :=
  (measurable_inv_sub_rclike z).stronglyMeasurable

private theorem integrable_centered_pow
    {𝕜 : Type*} [RCLike 𝕜]
    (μ : Measure ℝ) [IsFiniteMeasure μ] {c : 𝕜} {R : ℝ}
    (hμ : ∀ᵐ x : ℝ ∂μ, ‖(x : 𝕜) - c‖ ≤ R) (n : ℕ) :
    Integrable (fun x : ℝ => ((x : 𝕜) - c) ^ n) μ := by
  refine Integrable.mono' (integrable_const (R ^ n))
    (stronglyMeasurable_centered_pow c n).aestronglyMeasurable ?_
  filter_upwards [hμ] with x hx
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hx n

/-- Every centered remainder kernel is integrable outside an almost-everywhere
support ball.  This is the reusable integrability input behind the exact
finite Laurent identity. -/
theorem integrable_centered_pow_div_sub_of_ae_norm_sub_le
    {𝕜 : Type*} [RCLike 𝕜]
    (μ : Measure ℝ) [IsFiniteMeasure μ] {c z : 𝕜} {R : ℝ}
    (hR : 0 ≤ R) (hμ : ∀ᵐ x : ℝ ∂μ, ‖(x : 𝕜) - c‖ ≤ R)
    (hz : R < ‖z - c‖) (n : ℕ) :
    Integrable
      (fun x : ℝ => ((x : 𝕜) - c) ^ n / (z - (x : 𝕜))) μ := by
  refine Integrable.mono'
    (integrable_const (R ^ n / (‖z - c‖ - R)))
    (((stronglyMeasurable_centered_pow c n).mul
      (stronglyMeasurable_inv_sub z)).aestronglyMeasurable.congr
        (Filter.Eventually.of_forall fun x => (div_eq_mul_inv _ _).symm)) ?_
  filter_upwards [hμ] with x hx
  have hpow : ‖(x : 𝕜) - c‖ ^ n ≤ R ^ n :=
    pow_le_pow_left₀ (norm_nonneg _) hx n
  have hden : ‖z - c‖ - R ≤ ‖z - (x : 𝕜)‖ := by
    have h := norm_sub_norm_le (z - c) ((x : 𝕜) - c)
    have heq : (z - c) - ((x : 𝕜) - c) = z - (x : 𝕜) := by ring
    rw [heq] at h
    linarith
  rw [norm_div, norm_pow]
  exact div_le_div₀ (pow_nonneg hR n) hpow (sub_pos.mpr hz) hden

/-- The ordinary inverse Cauchy kernel is integrable outside an
almost-everywhere support ball. -/
theorem integrable_inv_sub_of_ae_norm_sub_le
    {𝕜 : Type*} [RCLike 𝕜]
    (μ : Measure ℝ) [IsFiniteMeasure μ] {c z : 𝕜} {R : ℝ}
    (hR : 0 ≤ R) (hμ : ∀ᵐ x : ℝ ∂μ, ‖(x : 𝕜) - c‖ ≤ R)
    (hz : R < ‖z - c‖) :
    Integrable (fun x : ℝ => (z - (x : 𝕜))⁻¹) μ := by
  simpa only [pow_zero, one_div] using
    (integrable_centered_pow_div_sub_of_ae_norm_sub_le
      μ hR hμ hz 0)

/-- A bounded-support estimate for every centered `RCLike`-valued moment of a
finite real measure:

`‖m_n(c)‖ ≤ R^n μ(ℝ)`.

The support condition is measure-theoretic: it is enough that
`‖(x : 𝕜) - c‖ ≤ R` almost everywhere. -/
theorem norm_measureCauchyMoment_le
    {𝕜 : Type*} [RCLike 𝕜]
    (μ : Measure ℝ) [IsFiniteMeasure μ] {c : 𝕜} {R : ℝ}
    (hμ : ∀ᵐ x : ℝ ∂μ, ‖(x : 𝕜) - c‖ ≤ R) (n : ℕ) :
    ‖measureCauchyMoment μ c n‖ ≤ R ^ n * μ.real Set.univ := by
  rw [measureCauchyMoment]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hμ] with x hx
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hx n

/-- **Exact finite Laurent expansion over an arbitrary real-or-complex
field.**

If a finite real measure is almost everywhere contained in the closed ball
`‖(x : 𝕜) - c‖ ≤ R` and `R < ‖z-c‖`, then its direct Cauchy-kernel integral is
the first `N` centered moments plus the displayed exact integral remainder. -/
theorem integral_inv_sub_eq_sum_range_measureCauchyMoment_add
    {𝕜 : Type*} [RCLike 𝕜]
    (μ : Measure ℝ) [IsFiniteMeasure μ] {c z : 𝕜} {R : ℝ}
    (hR : 0 ≤ R) (hμ : ∀ᵐ x : ℝ ∂μ, ‖(x : 𝕜) - c‖ ≤ R)
    (hz : R < ‖z - c‖) (N : ℕ) :
    (∫ x : ℝ, (z - (x : 𝕜))⁻¹ ∂μ) =
      (∑ k ∈ Finset.range N,
        measureCauchyMoment μ c k / (z - c) ^ (k + 1)) +
        ((z - c) ^ N)⁻¹ *
          ∫ x : ℝ, ((x : 𝕜) - c) ^ N / (z - (x : 𝕜)) ∂μ := by
  have hzc : z - c ≠ 0 := by
    apply norm_pos_iff.mp
    exact lt_of_le_of_lt hR hz
  have hintpow : ∀ k : ℕ,
      Integrable
        (fun x : ℝ => ((x : 𝕜) - c) ^ k / (z - c) ^ (k + 1)) μ := by
    intro k
    have h := (integrable_centered_pow μ hμ k).const_mul
      (((z - c) ^ (k + 1))⁻¹)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [division_def, mul_comm]
  have hintrem : Integrable
      (fun x : ℝ => ((x : 𝕜) - c) ^ N /
        ((z - c) ^ N * (z - (x : 𝕜)))) μ := by
    have h :=
      (integrable_centered_pow_div_sub_of_ae_norm_sub_le
        μ hR hμ hz N).const_mul
      (((z - c) ^ N)⁻¹)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [division_def, division_def, mul_inv]
    ring
  calc
    (∫ x : ℝ, (z - (x : 𝕜))⁻¹ ∂μ) =
        ∫ x : ℝ,
          ((∑ k ∈ Finset.range N,
              ((x : 𝕜) - c) ^ k / (z - c) ^ (k + 1)) +
            ((x : 𝕜) - c) ^ N /
              ((z - c) ^ N * (z - (x : 𝕜)))) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hμ] with x hx
      have hzx : z - (x : 𝕜) ≠ 0 := by
        apply norm_pos_iff.mp
        have h := norm_sub_norm_le (z - c) ((x : 𝕜) - c)
        have heq : (z - c) - ((x : 𝕜) - c) = z - (x : 𝕜) := by ring
        rw [heq] at h
        linarith
      exact inv_sub_eq_sum_range_add_centered N hzc hzx
    _ = (∑ k ∈ Finset.range N,
          ∫ x : ℝ,
            ((x : 𝕜) - c) ^ k / (z - c) ^ (k + 1) ∂μ) +
        ∫ x : ℝ, ((x : 𝕜) - c) ^ N /
          ((z - c) ^ N * (z - (x : 𝕜))) ∂μ := by
      rw [integral_add (integrable_finsetSum _ fun k _ => hintpow k)
        hintrem, integral_finsetSum _ fun k _ => hintpow k]
    _ = (∑ k ∈ Finset.range N,
          measureCauchyMoment μ c k / (z - c) ^ (k + 1)) +
        ((z - c) ^ N)⁻¹ *
          ∫ x : ℝ, ((x : 𝕜) - c) ^ N / (z - (x : 𝕜)) ∂μ := by
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        have hfun :
            (fun x : ℝ =>
              ((x : 𝕜) - c) ^ k / (z - c) ^ (k + 1)) =
              fun x : ℝ => ((z - c) ^ (k + 1))⁻¹ *
                ((x : 𝕜) - c) ^ k := by
          funext x
          rw [division_def, mul_comm]
        rw [hfun, MeasureTheory.integral_const_mul,
          measureCauchyMoment, division_def, mul_comm]
      · have hfun :
            (fun x : ℝ => ((x : 𝕜) - c) ^ N /
              ((z - c) ^ N * (z - (x : 𝕜)))) =
              fun x : ℝ => ((z - c) ^ N)⁻¹ *
                (((x : 𝕜) - c) ^ N / (z - (x : 𝕜))) := by
          funext x
          rw [division_def, division_def, mul_inv]
          ring
        rw [hfun, MeasureTheory.integral_const_mul]

/-- **Geometric bound for the generic exact finite Laurent remainder.**

Under the same bounded-support hypotheses, the error after `N` centered
moments is at most

`μ(ℝ) * (‖z-c‖-R)⁻¹ * (R / ‖z-c‖)^N`.

Thus the rate is geometric in `N`; the theorem also covers the zero measure
and radius `R = 0`. -/
theorem norm_integral_inv_sub_sub_sum_range_measureCauchyMoment_le
    {𝕜 : Type*} [RCLike 𝕜]
    (μ : Measure ℝ) [IsFiniteMeasure μ] {c z : 𝕜} {R : ℝ}
    (hR : 0 ≤ R) (hμ : ∀ᵐ x : ℝ ∂μ, ‖(x : 𝕜) - c‖ ≤ R)
    (hz : R < ‖z - c‖) (N : ℕ) :
    ‖(∫ x : ℝ, (z - (x : 𝕜))⁻¹ ∂μ) -
        ∑ k ∈ Finset.range N,
          measureCauchyMoment μ c k / (z - c) ^ (k + 1)‖ ≤
      μ.real Set.univ * (‖z - c‖ - R)⁻¹ *
        (R / ‖z - c‖) ^ N := by
  have hrem :
      (∫ x : ℝ, (z - (x : 𝕜))⁻¹ ∂μ) -
          ∑ k ∈ Finset.range N,
            measureCauchyMoment μ c k / (z - c) ^ (k + 1) =
        ((z - c) ^ N)⁻¹ *
          ∫ x : ℝ, ((x : 𝕜) - c) ^ N / (z - (x : 𝕜)) ∂μ := by
    rw [integral_inv_sub_eq_sum_range_measureCauchyMoment_add
      μ hR hμ hz N]
    ring
  rw [hrem, norm_mul, norm_inv, norm_pow]
  have hbound :
      ‖∫ x : ℝ, ((x : 𝕜) - c) ^ N / (z - (x : 𝕜)) ∂μ‖ ≤
        (R ^ N / (‖z - c‖ - R)) * μ.real Set.univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards [hμ] with x hx
    have hpow : ‖(x : 𝕜) - c‖ ^ N ≤ R ^ N :=
      pow_le_pow_left₀ (norm_nonneg _) hx N
    have hden : ‖z - c‖ - R ≤ ‖z - (x : 𝕜)‖ := by
      have h := norm_sub_norm_le (z - c) ((x : 𝕜) - c)
      have heq : (z - c) - ((x : 𝕜) - c) = z - (x : 𝕜) := by ring
      rw [heq] at h
      linarith
    rw [norm_div, norm_pow]
    exact div_le_div₀ (pow_nonneg hR N) hpow (sub_pos.mpr hz) hden
  calc
    (‖z - c‖ ^ N)⁻¹ *
        ‖∫ x : ℝ, ((x : 𝕜) - c) ^ N / (z - (x : 𝕜)) ∂μ‖ ≤
      (‖z - c‖ ^ N)⁻¹ *
        ((R ^ N / (‖z - c‖ - R)) * μ.real Set.univ) := by
      exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = μ.real Set.univ * (‖z - c‖ - R)⁻¹ *
        (R / ‖z - c‖) ^ N := by
      rw [div_pow, division_def]
      ring

/-- The centered-moment Laurent series of a bounded finite measure is
summable over every `RCLike` field at each point satisfying `R < ‖z-c‖`.
The comparison series has ratio `R / ‖z-c‖`. -/
theorem summable_measureCauchyMoment_laurent
    {𝕜 : Type*} [RCLike 𝕜]
    (μ : Measure ℝ) [IsFiniteMeasure μ] {c z : 𝕜} {R : ℝ}
    (hR : 0 ≤ R) (hμ : ∀ᵐ x : ℝ ∂μ, ‖(x : 𝕜) - c‖ ≤ R)
    (hz : R < ‖z - c‖) :
    Summable (fun k : ℕ =>
      measureCauchyMoment μ c k / (z - c) ^ (k + 1)) := by
  have hdpos : 0 < ‖z - c‖ := lt_of_le_of_lt hR hz
  have hq0 : 0 ≤ R / ‖z - c‖ := div_nonneg hR (norm_nonneg _)
  have hq1 : R / ‖z - c‖ < 1 :=
    (div_lt_one hdpos).mpr hz
  refine Summable.of_norm_bounded
    (g := fun k : ℕ =>
      (R / ‖z - c‖) ^ k * (μ.real Set.univ / ‖z - c‖))
    ((summable_geometric_of_lt_one hq0 hq1).mul_right _) fun k => ?_
  rw [norm_div, norm_pow]
  calc
    ‖measureCauchyMoment μ c k‖ / ‖z - c‖ ^ (k + 1) ≤
        (R ^ k * μ.real Set.univ) / ‖z - c‖ ^ (k + 1) := by
      exact div_le_div₀
        (mul_nonneg (pow_nonneg hR k) MeasureTheory.measureReal_nonneg)
        (norm_measureCauchyMoment_le μ hμ k) (by positivity) le_rfl
    _ = (R / ‖z - c‖) ^ k *
        (μ.real Set.univ / ‖z - c‖) := by
      rw [pow_succ, div_pow, division_def, mul_inv]
      ring

/-- **Convergent generic Laurent expansion of the direct Cauchy integral.**

For a finite real measure contained almost everywhere in the radius-`R` ball
about `c`, the direct integral equals the `tsum` of its centered moments
whenever `R < ‖z-c‖`. -/
theorem integral_inv_sub_eq_tsum_measureCauchyMoment
    {𝕜 : Type*} [RCLike 𝕜]
    (μ : Measure ℝ) [IsFiniteMeasure μ] {c z : 𝕜} {R : ℝ}
    (hR : 0 ≤ R) (hμ : ∀ᵐ x : ℝ ∂μ, ‖(x : 𝕜) - c‖ ≤ R)
    (hz : R < ‖z - c‖) :
    (∫ x : ℝ, (z - (x : 𝕜))⁻¹ ∂μ) =
      ∑' k : ℕ, measureCauchyMoment μ c k / (z - c) ^ (k + 1) := by
  have hsum := summable_measureCauchyMoment_laurent μ hR hμ hz
  have htend1 : Filter.Tendsto
      (fun N => ∑ k ∈ Finset.range N,
        measureCauchyMoment μ c k / (z - c) ^ (k + 1))
      Filter.atTop
      (nhds (∑' k : ℕ,
        measureCauchyMoment μ c k / (z - c) ^ (k + 1))) :=
    hsum.hasSum.tendsto_sum_nat
  have hq0 : 0 ≤ R / ‖z - c‖ :=
    div_nonneg hR (norm_nonneg _)
  have hq1 : R / ‖z - c‖ < 1 :=
    (div_lt_one (lt_of_le_of_lt hR hz)).mpr hz
  have hgeom : Filter.Tendsto
      (fun N : ℕ =>
        μ.real Set.univ * (‖z - c‖ - R)⁻¹ *
          (R / ‖z - c‖) ^ N)
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto
        (fun N : ℕ => (R / ‖z - c‖) ^ N)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) hq1
    have h1 := h0.const_mul
      (μ.real Set.univ * (‖z - c‖ - R)⁻¹)
    rw [mul_zero] at h1
    exact h1
  have htend2 : Filter.Tendsto
      (fun N => ∑ k ∈ Finset.range N,
        measureCauchyMoment μ c k / (z - c) ^ (k + 1))
      Filter.atTop
      (nhds (∫ x : ℝ, (z - (x : 𝕜))⁻¹ ∂μ)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun N => dist_nonneg) (fun N => ?_) hgeom
    rw [dist_eq_norm, norm_sub_rev]
    exact norm_integral_inv_sub_sub_sum_range_measureCauchyMoment_le
      μ hR hμ hz N
  exact tendsto_nhds_unique htend2 htend1

/-- `HasSum` form of the generic arbitrary-center bounded-support Laurent
expansion. -/
theorem hasSum_measureCauchyMoment_laurent
    {𝕜 : Type*} [RCLike 𝕜]
    (μ : Measure ℝ) [IsFiniteMeasure μ] {c z : 𝕜} {R : ℝ}
    (hR : 0 ≤ R) (hμ : ∀ᵐ x : ℝ ∂μ, ‖(x : 𝕜) - c‖ ≤ R)
    (hz : R < ‖z - c‖) :
    HasSum
      (fun k : ℕ =>
        measureCauchyMoment μ c k / (z - c) ^ (k + 1))
      (∫ x : ℝ, (z - (x : 𝕜))⁻¹ ∂μ) := by
  rw [integral_inv_sub_eq_tsum_measureCauchyMoment μ hR hμ hz]
  exact (summable_measureCauchyMoment_laurent μ hR hμ hz).hasSum

/-- Complex wrapper for the exact finite Laurent expansion of the named
oriented `measureCauchyTransform`. -/
theorem measureCauchyTransform_eq_sum_range_measureCauchyMoment_add
    (μ : Measure ℝ) [IsFiniteMeasure μ] {c z : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hμ : ∀ᵐ x : ℝ ∂μ, ‖(x : ℂ) - c‖ ≤ R)
    (hz : R < ‖z - c‖) (N : ℕ) :
    measureCauchyTransform μ z =
      (∑ k ∈ Finset.range N,
        measureCauchyMoment μ c k / (z - c) ^ (k + 1)) +
        ((z - c) ^ N)⁻¹ *
          ∫ x : ℝ, ((x : ℂ) - c) ^ N / (z - (x : ℂ)) ∂μ := by
  rw [measureCauchyTransform_apply]
  exact integral_inv_sub_eq_sum_range_measureCauchyMoment_add
    μ hR hμ hz N

/-- Complex wrapper for the geometric finite-remainder bound of the named
oriented `measureCauchyTransform`. -/
theorem norm_measureCauchyTransform_sub_sum_range_measureCauchyMoment_le
    (μ : Measure ℝ) [IsFiniteMeasure μ] {c z : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hμ : ∀ᵐ x : ℝ ∂μ, ‖(x : ℂ) - c‖ ≤ R)
    (hz : R < ‖z - c‖) (N : ℕ) :
    ‖measureCauchyTransform μ z -
        ∑ k ∈ Finset.range N,
          measureCauchyMoment μ c k / (z - c) ^ (k + 1)‖ ≤
      μ.real Set.univ * (‖z - c‖ - R)⁻¹ *
        (R / ‖z - c‖) ^ N := by
  rw [measureCauchyTransform_apply]
  exact norm_integral_inv_sub_sub_sum_range_measureCauchyMoment_le
    μ hR hμ hz N

/-- Complex wrapper for the convergent Laurent expansion of the named
oriented `measureCauchyTransform`. -/
theorem measureCauchyTransform_eq_tsum_measureCauchyMoment
    (μ : Measure ℝ) [IsFiniteMeasure μ] {c z : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hμ : ∀ᵐ x : ℝ ∂μ, ‖(x : ℂ) - c‖ ≤ R)
    (hz : R < ‖z - c‖) :
    measureCauchyTransform μ z =
      ∑' k : ℕ, measureCauchyMoment μ c k / (z - c) ^ (k + 1) := by
  rw [measureCauchyTransform_apply]
  exact integral_inv_sub_eq_tsum_measureCauchyMoment μ hR hμ hz

/-- `HasSum` wrapper for the centered-moment Laurent expansion of the named
oriented `measureCauchyTransform`. -/
theorem hasSum_measureCauchyTransform_measureCauchyMoment_laurent
    (μ : Measure ℝ) [IsFiniteMeasure μ] {c z : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hμ : ∀ᵐ x : ℝ ∂μ, ‖(x : ℂ) - c‖ ≤ R)
    (hz : R < ‖z - c‖) :
    HasSum
      (fun k : ℕ =>
        measureCauchyMoment μ c k / (z - c) ^ (k + 1))
      (measureCauchyTransform μ z) := by
  rw [measureCauchyTransform_apply]
  exact hasSum_measureCauchyMoment_laurent μ hR hμ hz

end Fabius

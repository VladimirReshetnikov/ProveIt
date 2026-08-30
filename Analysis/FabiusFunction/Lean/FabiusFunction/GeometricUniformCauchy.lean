import FabiusFunction.GeometricUniformLaw
import FabiusFunction.MeasureCauchyTransform

/-!
# Cauchy transforms of geometric uniform laws

This module specializes the generic affine fixed-point Cauchy calculus to the
geometrically weighted uniform series

`X_q = (1-q) U₀ + q X_q'`.

The transform and power hierarchy are total in `q`.  Holomorphy uses
`|q| < 1`; the divided differential equation and adjacent-power recurrence
also require `q ≠ 0`.  Negative ratios are included: the invariant carrier is
the exact range of `geometricUniformSeries q`, so no positivity or interval
support assumption is needed.

## Main results

* `analyticOn_geometricUniformStieltjesTransform` gives holomorphy off the
  exact support.
* `hasDerivAt_geometricUniformStieltjesTransform_refinement` is the
  general-`q` transform differential equation.
* `geometricUniformStieltjesPower_succ` is the adjacent-order resolvent
  hierarchy.
-/

set_option autoImplicit false

open MeasureTheory Set Complex

namespace Fabius

open ProbabilityRepresentation

/-- The natural domain of the geometric-law Stieltjes transform. -/
def geometricUniformStieltjesDomain (q : ℝ) : Set ℂ :=
  measureCauchyDomain (geometricUniformDistribution q)

/-- The oriented Cauchy--Stieltjes transform of the geometric uniform law. -/
noncomputable def geometricUniformStieltjesTransform (q : ℝ) : ℂ → ℂ :=
  measureCauchyTransform (geometricUniformDistribution q)

/-- The unnormalized Cauchy-power hierarchy of the geometric uniform law. -/
noncomputable def geometricUniformStieltjesPower
    (q : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  measureCauchyPower (geometricUniformDistribution q) n z

/-- Integral form of the geometric-law Stieltjes transform. -/
theorem geometricUniformStieltjesTransform_apply (q : ℝ) (z : ℂ) :
    geometricUniformStieltjesTransform q z =
      ∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂geometricUniformDistribution q := by
  exact measureCauchyTransform_apply (geometricUniformDistribution q) z

/-- Index one of the geometric Cauchy-power hierarchy is its transform. -/
@[simp] theorem geometricUniformStieltjesPower_one (q : ℝ) (z : ℂ) :
    geometricUniformStieltjesPower q 1 z =
      geometricUniformStieltjesTransform q z := by
  exact measureCauchyPower_one (geometricUniformDistribution q) z

/-- The natural geometric-law transform domain is open. -/
theorem isOpen_geometricUniformStieltjesDomain (q : ℝ) :
    IsOpen (geometricUniformStieltjesDomain q) :=
  isOpen_measureCauchyDomain (geometricUniformDistribution q)

/-- For `|q| < 1`, the geometric-law Stieltjes transform is holomorphic off
its exact topological support. -/
theorem analyticOn_geometricUniformStieltjesTransform
    {q : ℝ} (hq : |q| < 1) :
    AnalyticOn ℂ (geometricUniformStieltjesTransform q)
      (geometricUniformStieltjesDomain q) := by
  letI := geometricUniformDistribution_isProbabilityMeasure hq
  exact analyticOn_measureCauchyTransform (geometricUniformDistribution q)

private theorem geometricUniformCarrier_invariant
    {q : ℝ} (hq : |q| < 1) :
    ∀ u ∈ Icc (0 : ℝ) 1,
      ∀ x ∈ Set.range (geometricUniformSeries q),
        0 + (1 - q) * u + q * x ∈
          Set.range (geometricUniformSeries q) := by
  intro u hu x hx
  rcases hx with ⟨ω, rfl⟩
  let u' : Set.Icc (0 : ℝ) 1 := ⟨u, hu⟩
  let ω' : SampleSpace := fun
    | 0 => u'
    | n + 1 => ω n
  have htail : tail ω' = ω := by
    funext n
    rfl
  refine ⟨ω', ?_⟩
  calc
    geometricUniformSeries q ω' =
        (1 - q) * (ω' 0 : ℝ) +
          q * geometricUniformSeries q (tail ω') :=
      geometricUniformSeries_split hq ω'
    _ = 0 + (1 - q) * u + q * geometricUniformSeries q ω := by
      rw [htail]
      simp only [ω', u', zero_add]

/-- **General geometric-law Stieltjes refinement equation.**

For every real `q` with `|q| < 1` and `q ≠ 0`, including negative ratios,

`S_q'(z) = ((1-q)q)⁻¹
  (S_q(z/q) - S_q((z-(1-q))/q))`

throughout the complement of the exact support. -/
theorem hasDerivAt_geometricUniformStieltjesTransform_refinement
    {q : ℝ} (hq : |q| < 1) (hq0 : q ≠ 0)
    {z : ℂ} (hz : z ∈ geometricUniformStieltjesDomain q) :
    HasDerivAt (geometricUniformStieltjesTransform q)
      (((((1 - q) * q : ℝ) : ℂ)⁻¹) *
        (geometricUniformStieltjesTransform q (z / (q : ℂ)) -
          geometricUniformStieltjesTransform q
            ((z - ((1 - q : ℝ) : ℂ)) / (q : ℂ)))) z := by
  letI := geometricUniformDistribution_isProbabilityMeasure hq
  let K : Set ℝ := Set.range (geometricUniformSeries q)
  have hsupport : (geometricUniformDistribution q).support = K :=
    geometricUniformDistribution_support_eq_range hq
  have hzK : z ∉ algebraMap ℝ ℂ '' K := by
    rw [← hsupport]
    exact hz
  have ha : 1 - q ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (abs_lt.mp hq).2)
  have h := hasDerivAt_measureCauchyTransform_of_uniformAffineFixedPoint
    (geometricUniformDistribution q) (a := 1 - q) (b := q) (c := 0)
    ha hq0 (K := K) hsupport.le
    (geometricUniformCarrier_invariant hq)
    (by simpa only [zero_add] using
      geometricUniformDistribution_selfSimilar hq)
    hzK
  simpa only [geometricUniformStieltjesTransform, ofReal_zero, sub_zero]
    using h

/-- **Adjacent-order geometric resolvent hierarchy.**  For positive `n` and
every nonzero `q` in the open unit disk,

`S_(q,n+1)(z) = (n(1-q)q^n)⁻¹
  (S_(q,n)((z-(1-q))/q) - S_(q,n)(z/q))`.

The theorem includes negative real ratios. -/
theorem geometricUniformStieltjesPower_succ
    {q : ℝ} (hq : |q| < 1) (hq0 : q ≠ 0)
    (n : ℕ) (hn : n ≠ 0)
    {z : ℂ} (hz : z ∈ geometricUniformStieltjesDomain q) :
    geometricUniformStieltjesPower q (n + 1) z =
      (((n : ℂ) * ((1 - q : ℝ) : ℂ) * (q : ℂ) ^ n)⁻¹) *
        (geometricUniformStieltjesPower q n
            ((z - ((1 - q : ℝ) : ℂ)) / (q : ℂ)) -
          geometricUniformStieltjesPower q n (z / (q : ℂ))) := by
  letI := geometricUniformDistribution_isProbabilityMeasure hq
  let K : Set ℝ := Set.range (geometricUniformSeries q)
  have hsupport : (geometricUniformDistribution q).support = K :=
    geometricUniformDistribution_support_eq_range hq
  have hzK : z ∉ algebraMap ℝ ℂ '' K := by
    rw [← hsupport]
    exact hz
  have ha : 1 - q ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (abs_lt.mp hq).2)
  have h := measureCauchyPower_succ_of_uniformAffineFixedPoint
    (geometricUniformDistribution q) (a := 1 - q) (b := q) (c := 0)
    ha hq0 (K := K) hsupport.le
    (geometricUniformCarrier_invariant hq)
    (by simpa only [zero_add] using
      geometricUniformDistribution_selfSimilar hq)
    n hn hzK
  simpa only [geometricUniformStieltjesPower, ofReal_zero, sub_zero]
    using h

end Fabius

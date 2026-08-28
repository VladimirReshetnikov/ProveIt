import FabiusFunction.RandomSeriesLaw
import Mathlib.MeasureTheory.Measure.ResolventTransform

/-!
# Cauchy--Stieltjes transforms of the Fabius--Rvachev laws

This module connects the two canonical Fabius--Rvachev probability measures
to Mathlib's resolvent-transform calculus.  Mathlib uses the kernel
`(x - z)⁻¹`; the convention in the Fabius literature is the opposite
orientation `(z - x)⁻¹`, so both transforms below are the negatives of
`MeasureTheory.resolventTransform`.

The up-law transform is analytic off `[-1,1]`, the random-series transform is
analytic off `[0,1]`, and their first derivatives are the negatives of the
expected squared Cauchy kernels.  The affine equality in law
`X = (Y + 1) / 2` gives the exact bridge

`S(z) = 2 * R(2*z - 1)`.

This is deliberately a transform-calculus layer only.  It does not prove the
Rvachev resolvent differential equation, its all-order affine orbit, moment
expansions, boundary-value formulas, or continued fractions.

## Main results

* `rvachevCauchyTransform_apply` and
  `rvachevCauchyTransform_eq_integral_rvachevUp` give the measure and density
  forms of the up-law Cauchy transform.
* `analyticOn_rvachevCauchyTransform` and
  `analyticOn_fabiusStieltjesTransform` give the natural holomorphy domains.
* `hasDerivAt_rvachevCauchyTransform` and
  `hasDerivAt_fabiusStieltjesTransform` identify the first derivatives.
* `fabiusStieltjesTransform_eq_two_mul_rvachevCauchyTransform` is the affine
  bridge between the two laws.
-/

set_option autoImplicit false

open MeasureTheory Set spectrum Complex

namespace Fabius

open ProbabilityRepresentation

/-- The natural domain of the Cauchy transform of the up-law: the complement
of the complexified support interval `[-1,1]`. -/
def rvachevCauchyDomain : Set ℂ :=
  (algebraMap ℝ ℂ '' Icc (-1 : ℝ) 1)ᶜ

/-- The natural domain of the Stieltjes transform of the dyadic random-series
law: the complement of the complexified support interval `[0,1]`. -/
def fabiusStieltjesDomain : Set ℂ :=
  (algebraMap ℝ ℂ '' Icc (0 : ℝ) 1)ᶜ

/-- The Cauchy transform of the up-law in the literature's orientation
`R(z) = ∫ (z-x)⁻¹ dμ_up(x)`. -/
noncomputable def rvachevCauchyTransform (F : BoundedFabius) : ℂ → ℂ :=
  fun z => -MeasureTheory.resolventTransform (rvachevMeasure F) z

/-- The Stieltjes transform of the dyadic random-series law in the orientation
`S(z) = ∫ (z-x)⁻¹ dμ_X(x)`. -/
noncomputable def fabiusStieltjesTransform : ℂ → ℂ :=
  fun z => -MeasureTheory.resolventTransform weightedSumDistribution z

private theorem neg_resolvent_eq_inv_sub (z : ℂ) (x : ℝ) :
    -resolvent z x = (z - (x : ℂ))⁻¹ := by
  rw [resolvent, Ring.inverse_eq_inv]
  rw [← inv_neg]
  congr 1
  simp only [Complex.coe_algebraMap, sub_eq_add_neg, neg_add_rev, neg_neg]

private theorem resolvent_sq_eq_inv_sub_sq (z : ℂ) (x : ℝ) :
    resolvent z x ^ 2 = (z - (x : ℂ))⁻¹ ^ 2 := by
  have h := congrArg (fun w : ℂ => w ^ 2) (neg_resolvent_eq_inv_sub z x)
  simpa only [neg_sq] using h

/-- The up-law Cauchy transform is the integral of the oriented kernel
`(z-x)⁻¹`.  This identity is total; off the support it is the usual
integrable Cauchy transform. -/
theorem rvachevCauchyTransform_apply (F : BoundedFabius) (z : ℂ) :
    rvachevCauchyTransform F z =
      ∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂rvachevMeasure F := by
  rw [rvachevCauchyTransform, MeasureTheory.resolventTransform_apply,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  exact neg_resolvent_eq_inv_sub z x

/-- The random-series Stieltjes transform is the integral of the oriented
kernel `(z-x)⁻¹`. -/
theorem fabiusStieltjesTransform_apply (z : ℂ) :
    fabiusStieltjesTransform z =
      ∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂weightedSumDistribution := by
  rw [fabiusStieltjesTransform, MeasureTheory.resolventTransform_apply,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  exact neg_resolvent_eq_inv_sub z x

/-- Density form of the up-law Cauchy transform. -/
theorem rvachevCauchyTransform_eq_integral_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    rvachevCauchyTransform F z =
      ∫ x : ℝ, (rvachevUp F x : ℂ) * (z - (x : ℂ))⁻¹ := by
  rw [rvachevCauchyTransform_apply, rvachevMeasure,
    integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (rvachevUp_nonneg F x)]
    simp only [Complex.real_smul]
  · exact ENNReal.measurable_ofReal.comp
      (rvachev_contDiff F hF).continuous.measurable
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

private theorem support_weightedSumDistribution_subset_Icc :
    weightedSumDistribution.support ⊆ Icc (0 : ℝ) 1 := by
  apply Measure.support_subset_of_isClosed isClosed_Icc
  rw [mem_ae_iff]
  exact weightedSumDistribution_compl_Icc

/-- The complement of the complexified interval `[-1,1]` is open. -/
theorem isOpen_rvachevCauchyDomain : IsOpen rvachevCauchyDomain := by
  rw [rvachevCauchyDomain]
  simpa only [Complex.coe_algebraMap] using
    (isCompact_Icc.image Complex.continuous_ofReal).isClosed.isOpen_compl

/-- The complement of the complexified interval `[0,1]` is open. -/
theorem isOpen_fabiusStieltjesDomain : IsOpen fabiusStieltjesDomain := by
  rw [fabiusStieltjesDomain]
  simpa only [Complex.coe_algebraMap] using
    (isCompact_Icc.image Complex.continuous_ofReal).isClosed.isOpen_compl

/-- First derivative of the up-law Cauchy transform on its natural domain. -/
theorem hasDerivAt_rvachevCauchyTransform
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ}
    (hz : z ∈ rvachevCauchyDomain) :
    HasDerivAt (rvachevCauchyTransform F)
      (-(∫ x : ℝ, (z - (x : ℂ))⁻¹ ^ 2 ∂rvachevMeasure F)) z := by
  letI := rvachevMeasure_isProbability F hF
  have hz' : z ∉ algebraMap ℝ ℂ '' (rvachevMeasure F).support := by
    rw [support_rvachevMeasure F hF]
    exact hz
  have h := HasDerivAt.neg (𝕜 := ℂ) (F := ℂ)
    (MeasureTheory.hasDerivAt_resolventTransform
      (𝕜 := ℝ) (A := ℂ) z hz')
  have hsq :
      (∫ x : ℝ, resolvent z x ^ 2 ∂rvachevMeasure F) =
        ∫ x : ℝ, (z - (x : ℂ))⁻¹ ^ 2 ∂rvachevMeasure F := by
    apply integral_congr_ae
    filter_upwards with x
    exact resolvent_sq_eq_inv_sub_sq z x
  rw [hsq] at h
  simpa only [rvachevCauchyTransform] using! h

/-- First derivative of the random-series Stieltjes transform on its natural
domain. -/
theorem hasDerivAt_fabiusStieltjesTransform {z : ℂ}
    (hz : z ∈ fabiusStieltjesDomain) :
    HasDerivAt fabiusStieltjesTransform
      (-(∫ x : ℝ, (z - (x : ℂ))⁻¹ ^ 2 ∂weightedSumDistribution)) z := by
  have hz' : z ∉ algebraMap ℝ ℂ '' weightedSumDistribution.support := by
    intro hzsupport
    exact hz (image_mono support_weightedSumDistribution_subset_Icc hzsupport)
  have h := HasDerivAt.neg (𝕜 := ℂ) (F := ℂ)
    (MeasureTheory.hasDerivAt_resolventTransform
      (𝕜 := ℝ) (A := ℂ) z hz')
  have hsq :
      (∫ x : ℝ, resolvent z x ^ 2 ∂weightedSumDistribution) =
        ∫ x : ℝ, (z - (x : ℂ))⁻¹ ^ 2 ∂weightedSumDistribution := by
    apply integral_congr_ae
    filter_upwards with x
    exact resolvent_sq_eq_inv_sub_sq z x
  rw [hsq] at h
  simpa only [fabiusStieltjesTransform] using! h

/-- The up-law Cauchy transform is holomorphic off `[-1,1]`. -/
theorem analyticOn_rvachevCauchyTransform
    (F : BoundedFabius) (hF : IsFabius F) :
    AnalyticOn ℂ (rvachevCauchyTransform F) rvachevCauchyDomain := by
  letI := rvachevMeasure_isProbability F hF
  rw [Complex.analyticOn_iff_differentiableOn isOpen_rvachevCauchyDomain]
  · intro z hz
    exact (hasDerivAt_rvachevCauchyTransform F hF hz).differentiableAt
      |>.differentiableWithinAt

/-- The random-series Stieltjes transform is holomorphic off `[0,1]`. -/
theorem analyticOn_fabiusStieltjesTransform :
    AnalyticOn ℂ fabiusStieltjesTransform fabiusStieltjesDomain := by
  rw [Complex.analyticOn_iff_differentiableOn isOpen_fabiusStieltjesDomain]
  · intro z hz
    exact (hasDerivAt_fabiusStieltjesTransform hz).differentiableAt
      |>.differentiableWithinAt

/-- **Affine bridge between the two canonical transforms.**  The equality in
law `X = (Y+1)/2` turns the unit-interval Stieltjes transform into the up-law
Cauchy transform at the affine spectral parameter `2*z-1`.

The identity is total in Lean's Bochner-integral convention: a nonintegrable
integral is zero on both affinely equivalent sides.  Its analytic
Cauchy-transform interpretation is asserted only on the named domains. -/
theorem fabiusStieltjesTransform_eq_two_mul_rvachevCauchyTransform
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    fabiusStieltjesTransform z =
      2 * rvachevCauchyTransform F (2 * z - 1) := by
  rw [fabiusStieltjesTransform_apply,
    weightedSum_eq_map_rvachevMeasure F hF,
    integral_map_of_stronglyMeasurable]
  · rw [rvachevCauchyTransform_apply, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    have hden :
        2 * z - 1 - (y : ℂ) =
          2 * (z - (((y + 1) / 2 : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [hden, mul_inv]
    norm_num
    ring
  · exact (measurable_id.add_const 1).div_const 2
  · have hmeas : Measurable (-resolvent z) :=
      (MeasureTheory.measurable_resolvent
        (𝕜 := ℝ) (A := ℂ) (a := z)).neg
    have heq : -resolvent z = fun x : ℝ => (z - (x : ℂ))⁻¹ := by
      funext x
      exact neg_resolvent_eq_inv_sub z x
    rw [← heq]
    exact hmeas.stronglyMeasurable

/-- The affine bridge in the orientation used by the unit-interval reports:
`R(z) = ½ S((z+1)/2)`. -/
theorem rvachevCauchyTransform_eq_inv_two_mul_fabiusStieltjesTransform
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    rvachevCauchyTransform F z =
      (2 : ℂ)⁻¹ * fabiusStieltjesTransform ((z + 1) / 2) := by
  rw [fabiusStieltjesTransform_eq_two_mul_rvachevCauchyTransform F hF]
  have harg : 2 * ((z + 1) / 2) - 1 = z := by ring
  rw [harg]
  ring

end Fabius

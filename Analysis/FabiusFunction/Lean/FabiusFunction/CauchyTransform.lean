import FabiusFunction.GeometricUniformCauchy
import FabiusFunction.RandomSeriesLaw

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
logarithmic fixed-point equation, moment expansions, boundary-value formulas,
uniqueness, or continued fractions.

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
* `hasDerivAt_fabiusStieltjesTransform_refinement` is the dyadic
  unit-interval transform differential equation.
* `fabiusStieltjesPower_succ` and `rvachevCauchyPower_succ` give the two
  adjacent-order resolvent hierarchies.
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
  measureCauchyTransform (rvachevMeasure F)

/-- The Stieltjes transform of the dyadic random-series law in the orientation
`S(z) = ∫ (z-x)⁻¹ dμ_X(x)`. -/
noncomputable def fabiusStieltjesTransform : ℂ → ℂ :=
  measureCauchyTransform weightedSumDistribution

/-- The unnormalized Cauchy-power hierarchy of the up-law. -/
noncomputable def rvachevCauchyPower
    (F : BoundedFabius) (n : ℕ) (z : ℂ) : ℂ :=
  measureCauchyPower (rvachevMeasure F) n z

/-- The unnormalized Cauchy-power hierarchy of the dyadic random-series
law. -/
noncomputable def fabiusStieltjesPower (n : ℕ) (z : ℂ) : ℂ :=
  measureCauchyPower weightedSumDistribution n z

private theorem neg_resolvent_eq_inv_sub (z : ℂ) (x : ℝ) :
    -resolvent z x = (z - (x : ℂ))⁻¹ := by
  rw [resolvent, Ring.inverse_eq_inv]
  rw [← inv_neg]
  congr 1
  simp only [Complex.coe_algebraMap, sub_eq_add_neg,
    neg_add_rev, neg_neg]

/-- The up-law Cauchy transform is the integral of the oriented kernel
`(z-x)⁻¹`.  This identity is total; off the support it is the usual
integrable Cauchy transform. -/
theorem rvachevCauchyTransform_apply (F : BoundedFabius) (z : ℂ) :
    rvachevCauchyTransform F z =
      ∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂rvachevMeasure F := by
  exact measureCauchyTransform_apply (rvachevMeasure F) z

/-- The random-series Stieltjes transform is the integral of the oriented
kernel `(z-x)⁻¹`. -/
theorem fabiusStieltjesTransform_apply (z : ℂ) :
    fabiusStieltjesTransform z =
      ∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂weightedSumDistribution := by
  exact measureCauchyTransform_apply weightedSumDistribution z

/-- Index one of the up-law Cauchy-power hierarchy is its transform. -/
@[simp] theorem rvachevCauchyPower_one (F : BoundedFabius) (z : ℂ) :
    rvachevCauchyPower F 1 z = rvachevCauchyTransform F z := by
  exact measureCauchyPower_one (rvachevMeasure F) z

/-- Index one of the dyadic Cauchy-power hierarchy is its transform. -/
@[simp] theorem fabiusStieltjesPower_one (z : ℂ) :
    fabiusStieltjesPower 1 z = fabiusStieltjesTransform z := by
  exact measureCauchyPower_one weightedSumDistribution z

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
  have hz' : z ∈ measureCauchyDomain (rvachevMeasure F) := by
    rw [measureCauchyDomain, support_rvachevMeasure F hF]
    exact hz
  exact hasDerivAt_measureCauchyTransform (rvachevMeasure F) hz'

/-- First derivative of the random-series Stieltjes transform on its natural
domain. -/
theorem hasDerivAt_fabiusStieltjesTransform {z : ℂ}
    (hz : z ∈ fabiusStieltjesDomain) :
    HasDerivAt fabiusStieltjesTransform
      (-(∫ x : ℝ, (z - (x : ℂ))⁻¹ ^ 2 ∂weightedSumDistribution)) z := by
  have hz' : z ∈ measureCauchyDomain weightedSumDistribution := by
    rw [measureCauchyDomain, weightedSumDistribution_support_eq_Icc]
    exact hz
  exact hasDerivAt_measureCauchyTransform weightedSumDistribution hz'

/-- The up-law Cauchy transform is holomorphic off `[-1,1]`. -/
theorem analyticOn_rvachevCauchyTransform
    (F : BoundedFabius) (hF : IsFabius F) :
    AnalyticOn ℂ (rvachevCauchyTransform F) rvachevCauchyDomain := by
  letI := rvachevMeasure_isProbability F hF
  rw [Complex.analyticOn_iff_differentiableOn isOpen_rvachevCauchyDomain]
  intro z hz
  exact (hasDerivAt_rvachevCauchyTransform F hF hz).differentiableAt
    |>.differentiableWithinAt

/-- The random-series Stieltjes transform is holomorphic off `[0,1]`. -/
theorem analyticOn_fabiusStieltjesTransform :
    AnalyticOn ℂ fabiusStieltjesTransform fabiusStieltjesDomain := by
  rw [Complex.analyticOn_iff_differentiableOn isOpen_fabiusStieltjesDomain]
  intro z hz
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

/-- All-order affine bridge between the unit-interval and centered
Cauchy-power hierarchies:

`S_n(z) = 2^n R_n(2z-1)`. -/
theorem fabiusStieltjesPower_eq_two_pow_mul_rvachevCauchyPower
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (z : ℂ) :
    fabiusStieltjesPower n z =
      (2 : ℂ) ^ n * rvachevCauchyPower F n (2 * z - 1) := by
  have hmap :
      (rvachevMeasure F).map (fun y : ℝ => (y + 1) / 2) =
        (rvachevMeasure F).map
          (fun y : ℝ => (2 : ℝ)⁻¹ * y + (2 : ℝ)⁻¹) := by
    apply Measure.map_congr
    filter_upwards with y
    ring
  rw [fabiusStieltjesPower, rvachevCauchyPower,
    weightedSum_eq_map_rvachevMeasure F hF, hmap,
    measureCauchyPower_map_affine (rvachevMeasure F)
      (a := (2 : ℝ)⁻¹) (b := (2 : ℝ)⁻¹) (by norm_num)]
  congr 1
  · norm_num
  · push_cast
    norm_num
    ring_nf

/-- **Dyadic unit-interval Stieltjes refinement equation.**

`S'(z) = 4 (S(2z) - S(2z-1))` on `ℂ ∖ [0,1]`. -/
theorem hasDerivAt_fabiusStieltjesTransform_refinement
    {z : ℂ} (hz : z ∈ fabiusStieltjesDomain) :
    HasDerivAt fabiusStieltjesTransform
      (4 * (fabiusStieltjesTransform (2 * z) -
        fabiusStieltjesTransform (2 * z - 1))) z := by
  have hz' : z ∈ geometricUniformStieltjesDomain (1 / 2 : ℝ) := by
    rw [geometricUniformStieltjesDomain, measureCauchyDomain,
      geometricUniformDistribution_support_eq_Icc (by norm_num) (by norm_num)]
    exact hz
  have h := hasDerivAt_geometricUniformStieltjesTransform_refinement
    (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (z := z) hz'
  simp only [geometricUniformStieltjesTransform] at h
  rw [← weightedSumDistribution_eq_geometricUniformDistribution_one_half] at h
  have harg0 : z / (((1 / 2 : ℝ) : ℂ)) = 2 * z := by
    norm_num
    ring
  have harg1 :
      (z - (((1 - 1 / 2 : ℝ) : ℂ))) / (((1 / 2 : ℝ) : ℂ)) =
        2 * z - 1 := by
    norm_num
    ring
  have hcoeff :
      (((((1 - 1 / 2) * (1 / 2) : ℝ) : ℂ))⁻¹) = 4 := by
    norm_num
  rw [harg0, harg1, hcoeff] at h
  change HasDerivAt fabiusStieltjesTransform _ z at h
  apply h.congr_deriv
  rfl

private theorem half_add_one_mem_fabiusStieltjesDomain
    {z : ℂ} (hz : z ∈ rvachevCauchyDomain) :
    (z + 1) / 2 ∈ fabiusStieltjesDomain := by
  change z ∉ algebraMap ℝ ℂ '' Icc (-1 : ℝ) 1 at hz
  change (z + 1) / 2 ∉ algebraMap ℝ ℂ '' Icc (0 : ℝ) 1
  rintro ⟨x, hx, hxEq⟩
  apply hz
  rcases hx with ⟨hx0, hx1⟩
  refine ⟨2 * x - 1, ⟨by linarith, by linarith⟩, ?_⟩
  rw [Complex.coe_algebraMap] at hxEq ⊢
  calc
    (((2 * x - 1 : ℝ) : ℂ)) = 2 * (x : ℂ) - 1 := by norm_num
    _ = z := by rw [hxEq]; ring

/-- Adjacent-order dyadic unit-interval resolvent hierarchy:

`S_(n+1)(z) = (2^(n+1)/n) (S_n(2z-1) - S_n(2z))`. -/
theorem fabiusStieltjesPower_succ
    (n : ℕ) (hn : n ≠ 0) {z : ℂ} (hz : z ∈ fabiusStieltjesDomain) :
    fabiusStieltjesPower (n + 1) z =
      ((2 : ℂ) ^ (n + 1) / (n : ℂ)) *
        (fabiusStieltjesPower n (2 * z - 1) -
          fabiusStieltjesPower n (2 * z)) := by
  have hz' : z ∈ geometricUniformStieltjesDomain (1 / 2 : ℝ) := by
    rw [geometricUniformStieltjesDomain, measureCauchyDomain,
      geometricUniformDistribution_support_eq_Icc (by norm_num) (by norm_num)]
    exact hz
  have h := geometricUniformStieltjesPower_succ
    (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num) n hn
    (z := z) hz'
  simp only [geometricUniformStieltjesPower] at h
  rw [← weightedSumDistribution_eq_geometricUniformDistribution_one_half] at h
  have harg0 : z / (((1 / 2 : ℝ) : ℂ)) = 2 * z := by
    norm_num
    ring
  have harg1 :
      (z - (((1 - 1 / 2 : ℝ) : ℂ))) / (((1 / 2 : ℝ) : ℂ)) =
        2 * z - 1 := by
    norm_num
    ring
  have hcoeff :
      (((n : ℂ) * (((1 - 1 / 2 : ℝ) : ℂ)) *
        (((1 / 2 : ℝ) : ℂ)) ^ n)⁻¹) =
        (2 : ℂ) ^ (n + 1) / (n : ℂ) := by
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    norm_num
    rw [← inv_pow]
    norm_num
    rw [pow_succ, div_eq_mul_inv]
    ring
  rw [harg0, harg1, hcoeff] at h
  simpa only [fabiusStieltjesPower] using h

/-- Adjacent-order centered Rvachev resolvent hierarchy:

`R_(n+1)(z) = (2^n/n) (R_n(2z-1) - R_n(2z+1))`. -/
theorem rvachevCauchyPower_succ
    (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : n ≠ 0) {z : ℂ} (hz : z ∈ rvachevCauchyDomain) :
    rvachevCauchyPower F (n + 1) z =
      ((2 : ℂ) ^ n / (n : ℂ)) *
        (rvachevCauchyPower F n (2 * z - 1) -
          rvachevCauchyPower F n (2 * z + 1)) := by
  let w : ℂ := (z + 1) / 2
  have hw : w ∈ fabiusStieltjesDomain :=
    half_add_one_mem_fabiusStieltjesDomain hz
  have hS := fabiusStieltjesPower_succ n hn hw
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  calc
    rvachevCauchyPower F (n + 1) z =
        ((2 : ℂ) ^ (n + 1))⁻¹ * fabiusStieltjesPower (n + 1) w := by
      rw [fabiusStieltjesPower_eq_two_pow_mul_rvachevCauchyPower
        F hF (n + 1) w]
      dsimp only [w]
      have harg : 2 * ((z + 1) / 2) - 1 = z := by ring
      rw [harg]
      field_simp
    _ = ((2 : ℂ) ^ (n + 1))⁻¹ *
        (((2 : ℂ) ^ (n + 1) / (n : ℂ)) *
          (fabiusStieltjesPower n (2 * w - 1) -
            fabiusStieltjesPower n (2 * w))) := by rw [hS]
    _ = ((2 : ℂ) ^ n / (n : ℂ)) *
        (rvachevCauchyPower F n (2 * z - 1) -
          rvachevCauchyPower F n (2 * z + 1)) := by
      rw [fabiusStieltjesPower_eq_two_pow_mul_rvachevCauchyPower
          F hF n (2 * w - 1),
        fabiusStieltjesPower_eq_two_pow_mul_rvachevCauchyPower
          F hF n (2 * w)]
      dsimp only [w]
      field_simp
      ring_nf

end Fabius

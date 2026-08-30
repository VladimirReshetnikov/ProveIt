import FabiusFunction.StieltjesMomentLaurent
import FabiusFunction.MeasureRefinement

/-!
# Conditioning on the refinement

The one-step conditioning principle behind the transform layer's
fixed-point identities: writing the refinement as
`μ_up = (2⁻¹·)_*μ_up ∗ ν` with `ν` the uniform digit on `[-1/2,1/2]`,
any integrable kernel satisfies

`∫ f dμ_up = ∫ h(x'/2) dμ_up(x')`,

where `h(x)` is the digit average `∫ f(x+u) dν(u)`, evaluated in any
form that agrees almost everywhere on the rescaled support.  The
logarithmic fixed point and the resolvent hierarchy are two
instances; the principle is the entry point for the whole
entire-kernel calculus.

* `ae_map_mem_Ioo_half` — the rescaled tail lives in `(-1/2,1/2)`;
* `integral_eq_integral_digit_conditioning` — the principle.
-/

set_option autoImplicit false

open MeasureTheory Real Set

namespace Fabius

/-- The rescaled tail lives in `(-1/2, 1/2)`. -/
theorem ae_map_mem_Ioo_half (F : BoundedFabius) (hF : IsFabius F) :
    ∀ᵐ x ∂((rvachevMeasure F).map (2⁻¹ * ·)),
      x ∈ Ioo (-(2⁻¹ : ℝ)) 2⁻¹ := by
  refine (MeasureTheory.ae_map_iff
    (measurable_const_mul _).aemeasurable measurableSet_Ioo).mpr ?_
  filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x' hx'
  exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩

/-- **Conditioning on the refinement**: for integrable `f` and any
measurable `h` agreeing almost everywhere with the digit average
`x ↦ ∫ f(x+u) dν(u)` on the rescaled tail,
`∫ f dμ_up = ∫ h(x'/2) dμ_up(x')`. -/
theorem integral_eq_integral_digit_conditioning (F : BoundedFabius)
    (hF : IsFabius F) {f h : ℝ → ℝ}
    (hint : Integrable f (rvachevMeasure F))
    (hmeas : Measurable h)
    (hh : ∀ᵐ x ∂((rvachevMeasure F).map (2⁻¹ * ·)),
      ∫ u, f (x + u)
        ∂(volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) = h x) :
    ∫ x, f x ∂(rvachevMeasure F) =
      ∫ x', h (2⁻¹ * x') ∂(rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  haveI := isProbability_uniform_half
  haveI : IsProbabilityMeasure ((rvachevMeasure F).map (2⁻¹ * ·)) :=
    Measure.isProbabilityMeasure_map
      (measurable_const_mul _).aemeasurable
  have href : rvachevMeasure F =
      ((rvachevMeasure F).map (2⁻¹ * ·)) ∗
        (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) := by
    conv_lhs => rw [rvachevMeasure_refinement F hF]
    exact MeasureTheory.Measure.conv_comm _ _
  have hint' : Integrable f
      ((((rvachevMeasure F).map (2⁻¹ * ·)) ∗
        (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) : Measure ℝ)) := by
    rw [← href]
    exact hint
  calc ∫ x, f x ∂(rvachevMeasure F)
      = ∫ x, f x ∂((((rvachevMeasure F).map (2⁻¹ * ·)) ∗
          (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) : Measure ℝ)) := by
        rw [← href]
    _ = ∫ x, ∫ u, f (x + u)
          ∂(volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹))
          ∂((rvachevMeasure F).map (2⁻¹ * ·)) :=
        by exact MeasureTheory.integral_conv hint'
    _ = ∫ x, h x ∂((rvachevMeasure F).map (2⁻¹ * ·)) :=
        integral_congr_ae hh
    _ = ∫ x', h (2⁻¹ * x') ∂(rvachevMeasure F) := by
        rw [MeasureTheory.integral_map
          (measurable_const_mul _).aemeasurable
          hmeas.aestronglyMeasurable]

end Fabius

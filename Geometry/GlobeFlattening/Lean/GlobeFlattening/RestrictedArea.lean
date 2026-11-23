import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Restricted area of the good image

The Jacobian formula only needs differentiability on the measurable set
being mapped. Here that set is the good set of the construction.
-/

open MeasureTheory MeasureTheory.Measure Module Set
open scoped ENNReal

namespace GlobeFlattening

noncomputable section

/-- The triangular map keeps latitude and replaces longitude by the scalar
coordinate. -/
def flattenCoordinates (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (u p, p.2)

/-- The derivative is diagonal in the longitude and latitude coordinates. -/
def coordinateDerivative (slope : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (slope • ContinuousLinearMap.id ℝ ℝ).prodMap (ContinuousLinearMap.id ℝ ℝ)

@[simp] theorem det_coordinateDerivative (slope : ℝ) :
    (coordinateDerivative slope).det = slope := by
  simp [coordinateDerivative, ContinuousLinearMap.det, LinearMap.det_prodMap]

/-- The width-reparametrized chart has area density equal to its positive
longitude slope wherever the scalar derivative has the prescribed form. -/
theorem measure_flattened_good_image
    {domain good : Set (ℝ × ℝ)} {u : ℝ × ℝ → ℝ} {slope : ℝ × ℝ → ℝ}
    (hgood : MeasurableSet good) (hsub : good ⊆ domain) (hnull : volume (domain \ good) = 0)
    (hf : InjOn (flattenCoordinates u) domain)
    (hDeriv : ∀ p ∈ good,
      HasFDerivWithinAt u (slope p • ContinuousLinearMap.fst ℝ ℝ ℝ) domain p)
    (hnonneg : ∀ p ∈ good, 0 ≤ slope p) :
    volume (flattenCoordinates u '' good) = ∫⁻ p in domain, ENNReal.ofReal (slope p) := by
  rw [Measure.volume_eq_prod] at hnull ⊢
  have hrestrict := Measure.restrict_congr_set (hsub.eventuallyLE.antisymm (ae_le_set.2 hnull))
  rw [← hrestrict, ← lintegral_abs_det_fderiv_eq_addHaar_image
    (f := flattenCoordinates u) (f' := coordinateDerivative ∘ slope) (volume.prod volume) hgood
    (fun p hp => ((hDeriv p hp).mono hsub).prodMk hasFDerivAt_snd.hasFDerivWithinAt) (hf.mono hsub)]
  exact setLIntegral_congr_fun hgood fun p hp => by
    simp [abs_of_nonneg (hnonneg p hp)]

end

end GlobeFlattening

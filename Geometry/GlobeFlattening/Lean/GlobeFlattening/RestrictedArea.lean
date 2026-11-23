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

theorem injOn_flattenCoordinates {u : ℝ × ℝ → ℝ} {domain : Set (ℝ × ℝ)}
    (hmono : ∀ p ∈ domain, ∀ q ∈ domain, p.2 = q.2 → p.1 < q.1 → u p < u q) :
    InjOn (flattenCoordinates u) domain := by
  intro p hp q hq heq
  have hlat := congrArg (fun r : ℝ × ℝ => r.2) heq
  have hlon : u p = u q := congrArg (fun r : ℝ × ℝ => r.1) heq
  have hx : p.1 = q.1 := le_antisymm
    (le_of_not_gt fun h => (hmono q hq p hp hlat.symm h).ne hlon.symm)
    (le_of_not_gt fun h => (hmono p hp q hq hlat h).ne hlon)
  exact Prod.ext hx hlat

/-- The derivative is diagonal in the longitude and latitude coordinates. -/
def coordinateDerivative (slope : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (slope • ContinuousLinearMap.id ℝ ℝ).prodMap (ContinuousLinearMap.id ℝ ℝ)

theorem hasFDerivWithinAt_flattenCoordinates {u : ℝ × ℝ → ℝ} {domain : Set (ℝ × ℝ)}
    {p : ℝ × ℝ} {slope : ℝ}
    (h : HasFDerivWithinAt u (slope • ContinuousLinearMap.fst ℝ ℝ ℝ) domain p) :
    HasFDerivWithinAt (flattenCoordinates u) (coordinateDerivative slope) domain p := by
  exact h.prodMk hasFDerivAt_snd.hasFDerivWithinAt

@[simp] theorem det_coordinateDerivative (slope : ℝ) :
    (coordinateDerivative slope).det = slope := by
  change (LinearMap.prodMap (slope • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).det = slope
  rw [LinearMap.det_prodMap]
  simp

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
  letI : IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hrestrict : volume.restrict good = volume.restrict domain :=
    Measure.restrict_congr_set (ae_eq_set.2 ⟨by simp [sdiff_eq_empty.mpr hsub], hnull⟩)
  rw [← hrestrict]
  calc
    _ = ∫⁻ p in good, ENNReal.ofReal |(coordinateDerivative (slope p)).det| :=
      (lintegral_abs_det_fderiv_eq_addHaar_image volume hgood
        (fun p hp => hasFDerivWithinAt_flattenCoordinates ((hDeriv p hp).mono hsub))
        (hf.mono hsub)).symm
    _ = _ := setLIntegral_congr_fun hgood fun p hp => by
      rw [det_coordinateDerivative, abs_of_nonneg (hnonneg p hp)]

end

end GlobeFlattening

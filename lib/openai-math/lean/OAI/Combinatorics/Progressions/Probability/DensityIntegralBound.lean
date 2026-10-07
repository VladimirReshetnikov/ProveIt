import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem density_mul_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (D : X → ℝ) (hD : Integrable D μ) (f : X → ℂ)
    (hf : AEStronglyMeasurable f μ) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    Integrable (fun x => (D x : ℂ) * f x) μ :=
  hD.ofReal.mul_bdd hf (ae_of_all μ hbound)

theorem norm_density_integral_le_one {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (D : X → ℝ) (hD : Integrable D μ) (hD0 : ∀ x, 0 ≤ D x)
    (hDmass : (∫ x, D x ∂μ) = 1) (f : X → ℂ) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    ‖∫ x, (D x : ℂ) * f x ∂μ‖ ≤ 1 := by
  rw [← hDmass]
  apply norm_integral_le_of_norm_le hD
  apply ae_of_all
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hD0 x)]
  exact mul_le_of_le_one_right (hD0 x) (hbound x)

end Erdos3

end

end OAI

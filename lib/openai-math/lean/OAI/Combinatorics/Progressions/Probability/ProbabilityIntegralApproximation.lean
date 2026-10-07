import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem probability_integral_approximation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f g : X → ℂ)
    (hf : Integrable f μ) (hg : Integrable g μ) {η : ℝ}
    (he : ∀ x, ‖f x - g x‖ ≤ η) :
    ‖(∫ x, f x ∂μ) - ∫ x, g x ∂μ‖ ≤ η := by
  rw [← integral_sub hf hg]
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (ae_of_all μ he)

end Erdos3

end

end OAI

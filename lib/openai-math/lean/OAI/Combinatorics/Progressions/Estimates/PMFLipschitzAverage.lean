import OAI.Combinatorics.Progressions.Probability.PMFPointMassMixture

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {T X : Type*} [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

theorem pmf_integrable_of_norm_le (p : PMF T) (f : T → ℂ) {B : ℝ}
    (hf : ∀ t, ‖f t‖ ≤ B) : Integrable f p.toMeasure :=
  Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable B (ae_of_all _ hf)

theorem pmf_integral_lipschitz [PseudoMetricSpace X]
    (p : PMF T) (F : T → X → ℂ) (L : ℝ≥0) {B : ℝ}
    (hB : ∀ t x, ‖F t x‖ ≤ B) (hL : ∀ t, LipschitzWith L (F t)) :
    LipschitzWith L (fun x => ∫ t, F t x ∂p.toMeasure) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← integral_sub
    (pmf_integrable_of_norm_le p _ (fun t => hB t x))
    (pmf_integrable_of_norm_le p _ (fun t => hB t y))]
  have h := norm_integral_le_of_norm_le_const
    (ae_of_all p.toMeasure (fun t => by
      simpa only [dist_eq_norm] using (hL t).dist_le_mul x y))
  simpa only [probReal_univ, mul_one] using h

end Erdos3

end

end OAI

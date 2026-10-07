/- Modified for ProveIt: construct mapped probability instances explicitly
from measurability in Mathlib v4.32.0. Statements unchanged. -/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace Ω]

theorem probability_partial_map_integral_measurable
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → β) (hf : Measurable f)
    (φ : α × β → ℂ) (hφ : Measurable φ) :
    Measurable (fun a => ∫ x, φ (a, f x) ∂ν) := by
  have h : Measurable (fun p : α × Ω => φ (p.1, f p.2)) :=
    hφ.comp (measurable_fst.prodMk (hf.comp measurable_snd))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableSpace α] [MeasurableSpace β] in
theorem probability_partial_map_integral_norm_le
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → β)
    (φ : α × β → ℂ) {C : ℝ} (hC : ∀ p, ‖φ p‖ ≤ C) (a : α) :
    ‖∫ x, φ (a, f x) ∂ν‖ ≤ C := by
  simpa using norm_integral_le_of_norm_le_const
    (μ := ν) (Filter.Eventually.of_forall (fun x => hC (a, f x)))

theorem probability_partial_map_integral_integrable
    (μ : Measure α) [IsProbabilityMeasure μ]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → β) (hf : Measurable f)
    (φ : α × β → ℂ) (hφ : Measurable φ) {C : ℝ} (hC : ∀ p, ‖φ p‖ ≤ C) :
    Integrable (fun a => ∫ x, φ (a, f x) ∂ν) μ := by
  refine ⟨(probability_partial_map_integral_measurable ν f hf φ hφ).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := C) (Filter.Eventually.of_forall ?_)⟩
  exact probability_partial_map_integral_norm_le ν f φ hC

theorem probability_prod_map_integral
    (μ : Measure α) [IsProbabilityMeasure μ]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → β) (hf : Measurable f)
    (φ : α × β → ℂ) (hφ : Measurable φ) {C : ℝ} (hC : ∀ p, ‖φ p‖ ≤ C) :
    ∫ p, φ p ∂(μ.prod (ν.map f)) = ∫ a, ∫ x, φ (a, f x) ∂ν ∂μ := by
  have : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hi : Integrable φ (μ.prod (ν.map f)) :=
    ⟨hφ.aestronglyMeasurable, HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hC)⟩
  rw [integral_prod φ hi]
  apply integral_congr_ae
  filter_upwards [] with a
  exact integral_map_of_stronglyMeasurable hf
    (hφ.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable

theorem probability_prod_map_real_integral
    (μ : Measure α) [IsProbabilityMeasure μ]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → β) (hf : Measurable f)
    (φ : α × β → ℝ) (hφ : Measurable φ) {C : ℝ} (hC : ∀ p, ‖φ p‖ ≤ C) :
    ∫ p, φ p ∂(μ.prod (ν.map f)) = ∫ a, ∫ x, φ (a, f x) ∂ν ∂μ := by
  have : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hi : Integrable φ (μ.prod (ν.map f)) :=
    ⟨hφ.aestronglyMeasurable, HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hC)⟩
  rw [integral_prod φ hi]
  apply integral_congr_ae
  filter_upwards [] with a
  exact integral_map_of_stronglyMeasurable hf
    (hφ.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable

end Erdos3

end

end OAI

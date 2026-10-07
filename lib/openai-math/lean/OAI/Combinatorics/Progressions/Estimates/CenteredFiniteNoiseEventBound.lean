import OAI.Combinatorics.Progressions.Probability.JointProductiveMeasure

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Classical

theorem centeredFiniteProbabilityMeasure_noise_event_le
    {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (bad : Ω → Prop) {ε : ℝ}
    (hbound : ∀ c, (law c).mean (fun x => if bad x then 1 else 0) ≤ ε) :
    (centeredFiniteProbabilityMeasure μ law).real {z | bad z.2} ≤ ε := by
  have hevent : MeasurableSet {z : C × Ω | bad z.2} :=
    (Set.toFinite {x : Ω | bad x}).measurableSet.preimage measurable_snd
  rw [centeredFiniteProbabilityMeasure_real_event μ law hweight _ hevent]
  have hi := centeredFinite_mean_integrable μ law hweight
    (fun _ x => if bad x then (1 : ℝ) else 0) (fun _ => integrable_const _)
  calc
    _ ≤ ∫ _ : C, ε ∂μ := integral_mono hi (integrable_const ε) hbound
    _ = ε := by simp

end Erdos3

end

end OAI

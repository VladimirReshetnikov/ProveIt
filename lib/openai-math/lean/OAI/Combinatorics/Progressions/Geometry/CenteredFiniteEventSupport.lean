import OAI.Combinatorics.Progressions.Probability.JointProductiveMeasure

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (μ : Measure C) (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ x, Measurable (fun c => (law c).weight x))

theorem centeredFinite_event_measurableSet (event : Set (C × Ω))
    (hevent : ∀ x, MeasurableSet {c | (c,x) ∈ event}) : MeasurableSet event := by
  have hm : Measurable (fun z : C × Ω => if z ∈ event then (1 : ℝ) else 0) :=
    measurable_from_prod_countable_left
      (fun x => measurable_const.ite (hevent x) measurable_const)
  have he : event = (fun z : C × Ω => if z ∈ event then (1 : ℝ) else 0) ⁻¹' {1} := by
    ext z
    by_cases hz : z ∈ event <;> simp [hz]
  rw [he]
  exact hm (measurableSet_singleton 1)

include hweight in

theorem centeredFiniteProbabilityMeasure_real_event_of_support [IsProbabilityMeasure μ]
    (event test : Set (C × Ω)) (htest : MeasurableSet test)
    (heq : ∀ c x, 0 < (law c).weight x → ((c,x) ∈ event ↔ (c,x) ∈ test)) :
    (centeredFiniteProbabilityMeasure μ law).real event =
      ∫ c, (law c).mean (fun x => if (c,x) ∈ event then 1 else 0) ∂μ := by
  have hae : event =ᵐ[centeredFiniteProbabilityMeasure μ law] test :=
    (centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight).mono
      (fun z hz => propext (heq z.1 z.2 hz))
  rw [measureReal_def, measure_congr hae, ← measureReal_def,
    centeredFiniteProbabilityMeasure_real_event μ law hweight test htest]
  apply integral_congr_ae
  apply ae_of_all
  intro c
  unfold FiniteProbabilityWeights.mean
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : (law c).weight x = 0
  · simp only [hx, zero_mul]
  · have hpos := lt_of_le_of_ne ((law c).nonneg x) (Ne.symm hx)
    simp only [heq c x hpos]

include hweight in

theorem centeredFiniteProbabilityMeasure_real_event_le_of_support [IsProbabilityMeasure μ]
    (event test : Set (C × Ω)) (htest : MeasurableSet test)
    (heq : ∀ c x, 0 < (law c).weight x → ((c,x) ∈ event ↔ (c,x) ∈ test))
    {ε : ℝ} (hbound : ∀ c, (law c).mean (fun x => if (c,x) ∈ event then 1 else 0) ≤ ε) :
    (centeredFiniteProbabilityMeasure μ law).real event ≤ ε := by
  rw [centeredFiniteProbabilityMeasure_real_event_of_support μ law hweight event test htest heq]
  calc
    _ ≤ ∫ _ : C, ε ∂μ := by
      apply integral_mono_of_nonneg
      · exact ae_of_all μ (fun c => (law c).mean_nonneg (fun _ => by split_ifs <;> norm_num))
      · exact integrable_const ε
      · exact ae_of_all μ hbound
    _ = ε := by simp

end Erdos3

end

end OAI

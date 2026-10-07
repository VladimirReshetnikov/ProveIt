import OAI.Combinatorics.Progressions.Probability.DiagonalImageDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem cutoff_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hbound : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) : Integrable w μ := by
  apply (integrable_const (1 : ℝ)).mono' hw.aestronglyMeasurable
  filter_upwards [] with a
  rw [Real.norm_of_nonneg (hbound a).1]
  exact (hbound a).2

theorem cutoffMeasure_mass_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ℝ) (hw : Measurable w)
    (hbound : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) : (realDensityMeasure μ w).real Set.univ ≤ 1 := by
  have hi := cutoff_integrable μ w hw hbound
  rw [realDensityMeasure_real_univ μ w hi (fun a => (hbound a).1)]
  have h := integral_mono hi (integrable_const (1 : ℝ)) (fun a => (hbound a).2)
  simpa using h

theorem mappedTest_cutoff_error {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (w : Ω → ℝ) (hw : Measurable w)
    (hbound : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (U : Ω → X) (hU : Measurable U) (φ : X → ℝ) (hφ : Measurable φ)
    (hφbound : ∀ x, ‖φ x‖ ≤ 1) :
    |mappedTest μ U φ - mappedTest (realDensityMeasure μ w) U φ| ≤ ∫ a, 1 - w a ∂μ := by
  have hwi := cutoff_integrable μ w hw hbound
  have hgi := mappedTest_integrable μ U hU φ hφ hφbound
  have hwgi : Integrable (fun a => w a * φ (U a)) μ :=
    hwi.mul_bdd (hφ.comp hU).aestronglyMeasurable (Filter.Eventually.of_forall (fun a => hφbound _))
  change |(∫ a, φ (U a) ∂μ) - ∫ a, φ (U a) ∂realDensityMeasure μ w| ≤ _
  rw [realDensityMeasure_integral μ w hw (fun a => (hbound a).1), ← integral_sub hgi hwgi]
  have hrem : Integrable (fun a => 1 - w a) μ := (integrable_const (1 : ℝ)).sub hwi
  have hp (a : Ω) : ‖φ (U a) - w a * φ (U a)‖ ≤ 1 - w a := by
    rw [show φ (U a) - w a * φ (U a) = (1 - w a) * φ (U a) by ring, norm_mul,
      Real.norm_of_nonneg (sub_nonneg.mpr (hbound a).2)]
    exact (mul_le_mul_of_nonneg_left (hφbound _) (sub_nonneg.mpr (hbound a).2)).trans_eq (mul_one _)
  have h := norm_integral_le_of_norm_le hrem (Filter.Eventually.of_forall hp)
  rw [Real.norm_eq_abs] at h
  exact h

end Erdos3

end

end OAI

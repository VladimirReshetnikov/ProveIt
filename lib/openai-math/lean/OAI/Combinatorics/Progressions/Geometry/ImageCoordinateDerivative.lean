import OAI.Combinatorics.Progressions.Estimates.WeightedImageDerivative

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

theorem smooth_image_derivative_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → (ι → ℝ)) (hU : Measurable U)
    (φ : (ι → ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (z : ι → ℝ) :
    Integrable (fun a => fderiv ℝ φ (U a) z) μ := by
  have hc := hφ.continuous_fderiv (by simp)
  obtain ⟨K, hK⟩ := (hs.fderiv ℝ).exists_bound_of_continuous hc
  apply (integrable_const (K * ‖z‖)).mono'
    (((hc.clm_apply continuous_const).measurable.comp hU).aestronglyMeasurable)
  filter_upwards [] with a
  exact ((fderiv ℝ φ (U a)).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right (hK _) (norm_nonneg _))

theorem imageTranslationBound_of_coordinate_derivatives [DecidableEq ι]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → (ι → ℝ)) (hU : Measurable U) (B : ι → ℝ≥0)
    (hweak : ∀ (φ : (ι → ℝ) → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, ‖φ x‖ ≤ 1) → ∀ i,
      |∫ a, fderiv ℝ φ (U a) (Pi.single i 1) ∂μ| ≤ B i) :
    ImageTranslationBound μ U (∑ i, B i) := by
  apply imageTranslationBound_of_smooth_derivative μ U hU
  intro φ hc hs hb z
  have hi (i : ι) := smooth_image_derivative_integrable μ U hU φ hc hs (Pi.single i 1)
  have heq : (∫ a, fderiv ℝ φ (U a) z ∂μ) =
      ∑ i, z i * ∫ a, fderiv ℝ φ (U a) (Pi.single i 1) ∂μ := by
    calc
      (∫ a, fderiv ℝ φ (U a) z ∂μ) =
          ∫ a, ∑ i, z i * fderiv ℝ φ (U a) (Pi.single i 1) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with a
        exact continuousLinearMap_coordinate_sum _ _
      _ = ∑ i, z i * ∫ a, fderiv ℝ φ (U a) (Pi.single i 1) ∂μ := by
        rw [integral_finsetSum _ (fun i _ => (hi i).const_mul (z i))]
        simp only [integral_const_mul]
  rw [heq, ← Real.norm_eq_abs]
  apply (norm_sum_le _ _).trans
  rw [NNReal.coe_sum, Finset.sum_mul, dist_eq_norm, sub_zero]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  have hbi : ‖∫ a, fderiv ℝ φ (U a) (Pi.single i 1) ∂μ‖ ≤ (B i : ℝ) := hweak φ hc hs hb i
  calc
    ‖z i‖ * ‖∫ a, fderiv ℝ φ (U a) (Pi.single i 1) ∂μ‖ ≤ ‖z i‖ * (B i : ℝ) :=
      mul_le_mul_of_nonneg_left hbi (norm_nonneg _)
    _ ≤ (B i : ℝ) * ‖z‖ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (B i).coe_nonneg

end Erdos3

end

end OAI

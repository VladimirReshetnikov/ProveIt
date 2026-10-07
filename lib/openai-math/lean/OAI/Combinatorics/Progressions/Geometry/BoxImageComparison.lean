import OAI.Combinatorics.Progressions.Estimates.SmoothedImageTest

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

def ImageTranslationBound (μ : Measure Ω) (U : Ω → (ι → ℝ)) (H : ℝ≥0) : Prop :=
  ∀ (φ : (ι → ℝ) → ℝ), Measurable φ → (∀ x, ‖φ x‖ ≤ 1) → ∀ z,
    |mappedTest μ U (fun x => φ (x + z)) - mappedTest μ U φ| ≤ H * dist z 0

theorem box_image_comparison [DecidableEq ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (hmass : μ.real Set.univ ≤ 1) (U V : Ω → (ι → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (H_U H_V : ℝ≥0) (hTU : ImageTranslationBound μ U H_U) (hTV : ImageTranslationBound μ V H_V)
    {ε : ℝ} (hε : 0 ≤ ε) (hclose : ∀ᵐ a ∂μ, dist (U a) (V a) ≤ ε)
    (δ : ℝ) (hδ : 0 < δ) (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |mappedTest μ U φ - mappedTest μ V φ| ≤
      ((H_U : ℝ) + H_V) * δ + 2 * (Fintype.card ι : ℝ) * ε / δ := by
  have hu := mappedTest_box_error μ U hU δ hδ H_U φ hφ hbound (hTU φ hφ hbound)
  have hv := mappedTest_box_error μ V hV δ hδ H_V φ hφ hbound (hTV φ hφ hbound)
  have hLip := boxTestAverage_lipschitz δ hδ φ hφ hbound
  have hmid := coupled_mappedTest_difference μ hmass U V hU hV hε hclose
    (boxTestAverage δ φ) hLip.continuous.measurable (boxTestAverage_norm_le δ hδ φ hbound)
    (boxTestLipschitz (ι := ι) δ hδ) hLip
  have hu' : |mappedTest μ U φ - mappedTest μ U (boxTestAverage δ φ)| ≤ (H_U : ℝ) * δ := by
    rw [abs_sub_comm]
    exact hu
  calc
    |mappedTest μ U φ - mappedTest μ V φ| ≤
        |mappedTest μ U φ - mappedTest μ U (boxTestAverage δ φ)| +
        |mappedTest μ U (boxTestAverage δ φ) - mappedTest μ V φ| := abs_sub_le _ _ _
    _ ≤ |mappedTest μ U φ - mappedTest μ U (boxTestAverage δ φ)| +
        (|mappedTest μ U (boxTestAverage δ φ) - mappedTest μ V (boxTestAverage δ φ)| +
          |mappedTest μ V (boxTestAverage δ φ) - mappedTest μ V φ|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ (H_U : ℝ) * δ + ((boxTestLipschitz (ι := ι) δ hδ : ℝ) * ε + (H_V : ℝ) * δ) :=
      add_le_add hu' (add_le_add hmid hv)
    _ = ((H_U : ℝ) + H_V) * δ + 2 * (Fintype.card ι : ℝ) * ε / δ := by
      rw [boxTestLipschitz_coe]
      ring

end Erdos3

end

end OAI

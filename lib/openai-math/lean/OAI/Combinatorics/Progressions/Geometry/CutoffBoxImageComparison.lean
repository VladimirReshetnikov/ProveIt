import OAI.Combinatorics.Progressions.Estimates.CutoffImageTest

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

theorem cutoff_box_image_comparison (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hw01 : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (U V : Ω → (ι → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (H_U H_V : ℝ≥0) (hTU : ImageTranslationBound (realDensityMeasure μ w) U H_U)
    (hTV : ImageTranslationBound (realDensityMeasure μ w) V H_V)
    {ε η : ℝ} (hε : 0 ≤ ε) (hcut : (∫ a, 1 - w a ∂μ) ≤ η)
    (hclose : ∀ᵐ a ∂realDensityMeasure μ w, dist (U a) (V a) ≤ ε)
    (δ : ℝ) (hδ : 0 < δ) (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |mappedTest μ U φ - mappedTest μ V φ| ≤
      2 * η + ((H_U : ℝ) + H_V) * δ + 2 * (Fintype.card ι : ℝ) * ε / δ := by
  let : IsFiniteMeasure (realDensityMeasure μ w) :=
    realDensityMeasure_finite μ w (cutoff_integrable μ w hw hw01) (fun a => (hw01 a).1)
  have hsmall := box_image_comparison (realDensityMeasure μ w) (cutoffMeasure_mass_le_one μ w hw hw01)
    U V hU hV H_U H_V hTU hTV hε hclose δ hδ φ hφ hbound
  have hu := (mappedTest_cutoff_error μ w hw hw01 U hU φ hφ hbound).trans hcut
  have hv := (mappedTest_cutoff_error μ w hw hw01 V hV φ hφ hbound).trans hcut
  have hv' : |mappedTest (realDensityMeasure μ w) V φ - mappedTest μ V φ| ≤ η := by
    rw [abs_sub_comm]
    exact hv
  calc
    |mappedTest μ U φ - mappedTest μ V φ| ≤
        |mappedTest μ U φ - mappedTest (realDensityMeasure μ w) U φ| +
          |mappedTest (realDensityMeasure μ w) U φ - mappedTest μ V φ| := abs_sub_le _ _ _
    _ ≤ |mappedTest μ U φ - mappedTest (realDensityMeasure μ w) U φ| +
        (|mappedTest (realDensityMeasure μ w) U φ - mappedTest (realDensityMeasure μ w) V φ| +
          |mappedTest (realDensityMeasure μ w) V φ - mappedTest μ V φ|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ η + ((((H_U : ℝ) + H_V) * δ + 2 * (Fintype.card ι : ℝ) * ε / δ) + η) :=
      add_le_add hu (add_le_add hsmall hv')
    _ = 2 * η + ((H_U : ℝ) + H_V) * δ + 2 * (Fintype.card ι : ℝ) * ε / δ := by ring

theorem sqrt_smoothing_balance {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    b * Real.sqrt (ε / b) + ε / Real.sqrt (ε / b) = 2 * Real.sqrt (b * ε) := by
  let d := Real.sqrt (ε / b)
  have hd : 0 < d := Real.sqrt_pos.mpr (div_pos hε hb)
  have hsq : d ^ 2 = ε / b := Real.sq_sqrt (div_nonneg hε.le hb.le)
  have hbd : b * d ^ 2 = ε := by
    rw [hsq]
    field_simp
  have hdiv : ε / d = b * d := (div_eq_iff hd.ne').mpr (by nlinarith [hbd])
  have hprod : (b * d) ^ 2 = b * ε := by
    calc
      (b * d) ^ 2 = b * (b * d ^ 2) := by ring
      _ = b * ε := by rw [hbd]
  have hroot : b * d = Real.sqrt (b * ε) := by
    nlinarith [Real.sq_sqrt (mul_pos hb hε).le, Real.sqrt_nonneg (b * ε), mul_pos hb hd]
  change b * d + ε / d = _
  rw [hdiv, hroot]
  ring

theorem cutoff_box_image_comparison_sqrt (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hw01 : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (U V : Ω → (ι → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (B : ℝ≥0) (hB : 0 < (B : ℝ))
    (hTU : ImageTranslationBound (realDensityMeasure μ w) U ((Fintype.card ι : ℝ≥0) * B))
    (hTV : ImageTranslationBound (realDensityMeasure μ w) V ((Fintype.card ι : ℝ≥0) * B))
    {ε η : ℝ} (hε : 0 < ε) (hcut : (∫ a, 1 - w a ∂μ) ≤ η)
    (hclose : ∀ᵐ a ∂realDensityMeasure μ w, dist (U a) (V a) ≤ ε)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |mappedTest μ U φ - mappedTest μ V φ| ≤
      2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt ((B : ℝ) * ε) := by
  have h := cutoff_box_image_comparison μ w hw hw01 U V hU hV _ _ hTU hTV hε.le hcut hclose
    (Real.sqrt (ε / (B : ℝ))) (Real.sqrt_pos.mpr (div_pos hε hB)) φ hφ hbound
  apply h.trans_eq
  have hbal := sqrt_smoothing_balance hB hε
  push_cast
  calc
    2 * η + ((Fintype.card ι : ℝ) * B + (Fintype.card ι : ℝ) * B) * Real.sqrt (ε / (B : ℝ)) +
        2 * (Fintype.card ι : ℝ) * ε / Real.sqrt (ε / (B : ℝ)) =
      2 * η + 2 * (Fintype.card ι : ℝ) *
        ((B : ℝ) * Real.sqrt (ε / (B : ℝ)) + ε / Real.sqrt (ε / (B : ℝ))) := by ring
    _ = 2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt ((B : ℝ) * ε) := by rw [hbal]; ring

end Erdos3

end

end OAI

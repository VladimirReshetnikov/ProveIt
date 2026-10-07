import Mathlib.MeasureTheory.Integral.Bochner.Basic
import OAI.Combinatorics.Progressions.Estimates.PositiveWeightNormalization

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem weight_div_range_of_lower {E : Type*} (w : E → ℝ) {B η : ℝ≥0} {Z : ℝ}
    (hη : 0 < η) (hZ : (η : ℝ) ≤ Z) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (x : E) :
    0 ≤ w x / Z ∧ w x / Z ≤ (B / η : ℝ≥0) := by
  have hη' : (0 : ℝ) < η := hη
  have hZ' : 0 < Z := hη'.trans_le hZ
  refine ⟨div_nonneg (hw x).1 hZ'.le, ?_⟩
  calc
    w x / Z ≤ (B : ℝ) / Z := div_le_div_of_nonneg_right (hw x).2 hZ'.le
    _ ≤ (B : ℝ) / η := div_le_div_of_nonneg_left B.coe_nonneg hη' hZ
    _ = _ := (NNReal.coe_div B η).symm

theorem weight_div_lipschitz_of_lower {E : Type*} [PseudoMetricSpace E]
    (w : E → ℝ) {T η : ℝ≥0} {Z : ℝ} (hη : 0 < η) (hZ : (η : ℝ) ≤ Z)
    (hw : LipschitzWith T w) : LipschitzWith (T / η) (fun x => w x / Z) := by
  have hη' : (0 : ℝ) < η := hη
  have hZ' : 0 < Z := hη'.trans_le hZ
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hZ']
  have hxy := hw.dist_le_mul x y
  rw [Real.dist_eq] at hxy
  calc
    |w x - w y| / Z ≤ ((T : ℝ) * dist x y) / Z := div_le_div_of_nonneg_right hxy hZ'.le
    _ ≤ ((T : ℝ) * dist x y) / η :=
      div_le_div_of_nonneg_left (mul_nonneg T.coe_nonneg dist_nonneg) hη' hZ
    _ = (T / η : ℝ≥0) * dist x y := by rw [NNReal.coe_div]; ring

theorem integral_weight_div_self {E : Type*} [MeasurableSpace E] (μ : Measure E) (w : E → ℝ)
    (h : (∫ x, w x ∂μ) ≠ 0) : (∫ x, w x / (∫ y, w y ∂μ) ∂μ) = 1 := by
  rw [integral_div, div_self h]

end Erdos3

end

end OAI

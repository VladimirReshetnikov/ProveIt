import Mathlib.Analysis.Complex.Basic
import OAI.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem rectangularLatticePoint_add_displacement {I : Type*} [Fintype I]
    (a S : I → ℝ) (x v : I → ℤ) :
    rectangularLatticePoint a S (x + v) - rectangularLatticePoint a S x =
      rectangularLatticePoint 0 S v := by
  funext i
  simp only [rectangularLatticePoint, Pi.sub_apply, Pi.add_apply, Pi.zero_apply,
    Int.cast_add]
  ring

theorem normalizedSpatialAmplitude_shift_le {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] (F : (I → ℝ) → E) {L : ℝ≥0}
    (hF : LipschitzWith L F) (a S : I → ℝ) (x v : I → ℤ) :
    ‖F (rectangularLatticePoint a S (x + v)) - F (rectangularLatticePoint a S x)‖ ≤
      L * ‖rectangularLatticePoint 0 S v‖ := by
  have h := hF.norm_sub_le (rectangularLatticePoint a S (x + v))
    (rectangularLatticePoint a S x)
  rwa [rectangularLatticePoint_add_displacement] at h

theorem normalizedSpatialAmplitude_shift_le_of_norm_le {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] (F : (I → ℝ) → E) {L : ℝ≥0}
    (hF : LipschitzWith L F) (a S : I → ℝ) (x v : I → ℤ)
    {r : ℝ} (hv : ‖rectangularLatticePoint 0 S v‖ ≤ r) :
    ‖F (rectangularLatticePoint a S (x + v)) - F (rectangularLatticePoint a S x)‖ ≤
      L * r :=
  (normalizedSpatialAmplitude_shift_le F hF a S x v).trans
    (mul_le_mul_of_nonneg_left hv L.coe_nonneg)

theorem normalizedSpatialRealAmplitude_cast_shift_le {I : Type*} [Fintype I]
    (F : (I → ℝ) → ℝ) {L : ℝ≥0} (hF : LipschitzWith L F)
    (a S : I → ℝ) (x v : I → ℤ) {r : ℝ}
    (hv : ‖rectangularLatticePoint 0 S v‖ ≤ r) :
    ‖(F (rectangularLatticePoint a S (x + v)) : ℂ) -
        (F (rectangularLatticePoint a S x) : ℂ)‖ ≤ L * r := by
  rw [← Complex.ofReal_sub, Complex.norm_real]
  exact normalizedSpatialAmplitude_shift_le_of_norm_le F hF a S x v hv

end Erdos3

end

end OAI

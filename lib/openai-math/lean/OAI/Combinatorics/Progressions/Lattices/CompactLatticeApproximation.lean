import OAI.Combinatorics.Progressions.Estimates.CompactIntervalIntegral
import OAI.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem sampledWeightHistogram_error (ψ : ℝ → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L ψ)
    {a S R : ℝ} (hS : 0 < S) (hsupport : ∀ x, R < |x| → ψ x = 0) (x : ℝ) :
    ‖sampledWeightHistogram ψ a S R x - ψ x‖ ≤ (L : ℝ) / S := by
  rw [sampledWeightHistogram_eq ψ hS hsupport]
  calc
    _ ≤ (L : ℝ) * ‖latticeSample a S x - x‖ := hLip.norm_sub_le _ _
    _ ≤ (L : ℝ) * (1 / S) :=
      mul_le_mul_of_nonneg_left (latticeSample_error hS x) L.coe_nonneg
    _ = _ := by ring

theorem sampledWeightHistogram_zero_outside (ψ : ℝ → ℝ) {a S R : ℝ}
    (hS : 1 ≤ S) (hsupport : ∀ x, R < |x| → ψ x = 0) (x : ℝ) (hx : R + 1 < |x|) :
    sampledWeightHistogram ψ a S R x = 0 := by
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have he : |latticeSample a S x - x| ≤ 1 :=
    (latticeSample_error hSp x).trans ((div_le_one hSp).mpr hS)
  have ht : |x| ≤ |latticeSample a S x| + |latticeSample a S x - x| := by
    have h := abs_sub_le x (latticeSample a S x) 0
    simpa only [sub_zero, abs_sub_comm x (latticeSample a S x), add_comm] using h
  rw [sampledWeightHistogram_eq ψ hSp hsupport]
  exact hsupport _ (by linarith)

theorem sampledWeightHistogram_l1_error (ψ : ℝ → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L ψ)
    {a S R : ℝ} (hR : 0 ≤ R) (hS : 1 ≤ S) (hsupport : ∀ x, R < |x| → ψ x = 0) :
    (∫ x, ‖sampledWeightHistogram ψ a S R x - ψ x‖) ≤ (2 * R + 2) * (L : ℝ) / S := by
  have hz : ∀ x, x ∉ Set.Icc (-(R + 1)) (R + 1) →
      sampledWeightHistogram ψ a S R x - ψ x = 0 := by
    intro x hx
    have hx' : R + 1 < |x| := lt_of_not_ge (fun h => hx (abs_le.mp h))
    rw [sampledWeightHistogram_zero_outside ψ hS hsupport x hx', hsupport x (by linarith), sub_self]
  have he := integral_norm_le_interval (fun x => sampledWeightHistogram ψ a S R x - ψ x)
    (u := -(R + 1)) (v := R + 1) (C := (L : ℝ) / S) (by linarith)
    hz (fun x _ => sampledWeightHistogram_error ψ hLip
      (lt_of_lt_of_le zero_lt_one hS) hsupport x)
  exact he.trans_eq (by ring)

theorem sampledWeightSum_error (ψ : ℝ → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L ψ)
    {a S R : ℝ} (hR : 0 ≤ R) (hS : 1 ≤ S) (hsupport : ∀ x, R < |x| → ψ x = 0) :
    |sampledWeightSum ψ a S R / S - ∫ x, ψ x| ≤ (2 * R + 2) * (L : ℝ) / S := by
  rw [← sampledWeightHistogram_integral ψ a (lt_of_lt_of_le zero_lt_one hS) R,
    ← integral_sub (sampledWeightHistogram_integrable ψ a S R)
      (compactInterval_integrable ψ hLip.continuous R hsupport)]
  exact (norm_integral_le_integral_norm _).trans
    (sampledWeightHistogram_l1_error ψ hLip hR hS hsupport)

end Erdos3

end

end OAI

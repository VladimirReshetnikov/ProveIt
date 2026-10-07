import OAI.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

theorem normalizedFiberDensity_law {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    {f : (J → ℝ) × (I → ℝ) → ℝ} (hf : Integrable f) (hf0 : ∀ p, 0 ≤ f p) :
    Measure.map (fun p : (J → ℝ) × (I → ℝ) =>
      normalizedIntegerPivot A S P *ᵥ p.2 + normalizedIntegerColumns B T P *ᵥ p.1)
      (realDensityMeasure volume f) =
      realDensityMeasure volume (normalizedFiberDensity A hA B S P T hS hP f) := by
  have he : (fun p : (J → ℝ) × (I → ℝ) =>
      (normalizedPivotEquiv A hA S P hS hP) p.2 +
        matrixSupCLM (normalizedIntegerColumns B T P) p.1) =
      fun p : (J → ℝ) × (I → ℝ) =>
        normalizedIntegerPivot A S P *ᵥ p.2 + normalizedIntegerColumns B T P *ᵥ p.1 := by
    funext p
    change (normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap p.2 + _ = _
    rw [normalizedPivotEquiv_coe, matrixSupCLM_apply, matrixSupCLM_apply]
  rw [← he]
  exact pivotOutputDensity_law _ _ hf hf0

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotOutputDensity_abs_le (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ)
    {R H : ℝ} (hR : 0 ≤ R) (hsupport : ∀ p, R < ‖p‖ → f p = 0)
    (hbound : ∀ p, ‖f p‖ ≤ H) (v : I → ℝ) :
    |pivotOutputDensity A B f v| ≤ inverseJacobian A * H * (2 * R) ^ Fintype.card J := by
  have hi := integral_norm_le_box (pivotSliceProfile A B f v) hR
    (pivotSliceProfile_zero_outside A B hsupport v) (fun y _ => hbound _)
  have hb := (norm_integral_le_integral_norm (f := pivotSliceProfile A B f v)).trans hi
  rw [pivotOutputDensity_slice_formula, abs_mul, abs_of_pos (inverseJacobian_pos A)]
  have h := mul_le_mul_of_nonneg_left hb (inverseJacobian_pos A).le
  simpa only [Real.norm_eq_abs, mul_assoc] using h

theorem pivotOutputDensity_abs_le_uniform [DecidableEq I]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (f : (J → ℝ) × (I → ℝ) → ℝ) {R H U : ℝ} (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hbound : ∀ p, ‖f p‖ ≤ H)
    (hinv : ‖A.symm.toContinuousLinearMap‖ ≤ U) (v : I → ℝ) :
    |pivotOutputDensity A B f v| ≤
      ((Fintype.card I).factorial * U ^ Fintype.card I) * H * (2 * R) ^ Fintype.card J :=
  (pivotOutputDensity_abs_le A B f hR hsupport hbound v).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (inverseJacobian_le_norm_bound A hinv) hH) (by positivity))

end Erdos3

end

end OAI

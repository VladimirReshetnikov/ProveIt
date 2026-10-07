import OAI.Combinatorics.Progressions.Estimates.PivotOutputLipschitz

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def pivotKernelCap {I : Type*} [Fintype I] (J : Type*) [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (R H : ℝ≥0) : ℝ≥0 :=
  ⟨inverseJacobian A, (inverseJacobian_pos A).le⟩ * H * (2*R)^Fintype.card J

noncomputable def pivotKernelLip {I : Type*} [Fintype I] (J : Type*) [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (R K : ℝ≥0) : ℝ≥0 :=
  pivotKernelCap J A R K * ‖A.symm.toContinuousLinearMap‖₊

theorem pivotOutputDensity_norm_le_cap {I J : Type*} [Fintype I] [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (f : (J → ℝ) × (I → ℝ) → ℝ) (R H : ℝ≥0)
    (hs : ∀ p, (R : ℝ) < ‖p‖ → f p = 0) (hb : ∀ p, ‖f p‖ ≤ H) (v : I → ℝ) :
    ‖pivotOutputDensity A B f v‖ ≤ pivotKernelCap J A R H := by
  change ‖pivotOutputDensity A B f v‖ ≤ inverseJacobian A * (H : ℝ) * (2*(R : ℝ))^Fintype.card J
  exact pivotOutputDensity_abs_le A B f R.coe_nonneg hs hb v

theorem pivotOutputDensity_lipschitz {I J : Type*} [Fintype I] [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} (R K : ℝ≥0) (hf : LipschitzWith K f)
    (hs : ∀ p, (R : ℝ) < ‖p‖ → f p = 0) :
    LipschitzWith (pivotKernelLip J A R K) (pivotOutputDensity A B f) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq, dist_eq_norm]
  apply (pivotOutputDensity_output_bound A B hf R.coe_nonneg hs v w).trans_eq
  change _ = (inverseJacobian A * (K : ℝ) * (2*(R : ℝ))^Fintype.card J *
    ‖A.symm.toContinuousLinearMap‖) * ‖v-w‖
  ring

end Erdos3

end

end OAI

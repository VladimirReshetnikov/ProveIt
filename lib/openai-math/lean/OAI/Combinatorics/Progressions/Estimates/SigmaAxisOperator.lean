import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import OAI.Combinatorics.Progressions.Geometry.SigmaAxisCoordinates

namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] {I O P : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)] [∀ d, Fintype (P d)]

noncomputable def sigmaAxisOperator (A : ∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ)) :
    ((Σ d, I d) → ℝ) →L[ℝ] ((Σ d, O d) → ℝ) :=
  ContinuousLinearMap.pi (fun s => (ContinuousLinearMap.proj s.2).comp
    ((A s.1).comp (sigmaAxisProjection I s.1)))

omit [Fintype D] [∀ d, Fintype (I d)] [∀ d, Fintype (O d)] in
theorem sigmaAxisOperator_apply (A : ∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ))
    (x : (Σ d, I d) → ℝ) (s : Σ d, O d) :
    sigmaAxisOperator A x s = A s.1 (sigmaAxisProjection I s.1 x) s.2 := rfl

omit [Fintype D] [∀ d, Fintype (I d)] [∀ d, Fintype (O d)] in
theorem sigmaAxisProjection_operator (A : ∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ))
    (x : (Σ d, I d) → ℝ) (d : D) :
    sigmaAxisProjection O d (sigmaAxisOperator A x) = A d (sigmaAxisProjection I d x) := rfl

omit [Fintype D] [∀ d, Fintype (I d)] [∀ d, Fintype (O d)] [∀ d, Fintype (P d)] in
theorem sigmaAxisOperator_comp (A : ∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ))
    (B : ∀ d, (O d → ℝ) →L[ℝ] (P d → ℝ)) :
    (sigmaAxisOperator B).comp (sigmaAxisOperator A) =
      sigmaAxisOperator (fun d => (B d).comp (A d)) := by
  ext x s
  rfl

omit [Fintype D] [∀ d, Fintype (I d)] in
theorem sigmaAxisOperator_id :
    sigmaAxisOperator (fun d => ContinuousLinearMap.id ℝ (I d → ℝ)) =
      ContinuousLinearMap.id ℝ ((Σ d, I d) → ℝ) := by
  ext x s
  rfl

theorem sigmaAxisOperator_norm_le (A : ∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ))
    {K : ℝ} (hK : 0 ≤ K) (hA : ∀ d, ‖A d‖ ≤ K) : ‖sigmaAxisOperator A‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg x))).mpr
  intro s
  calc
    ‖sigmaAxisOperator A x s‖ ≤ ‖A s.1 (sigmaAxisProjection I s.1 x)‖ := norm_le_pi_norm _ s.2
    _ ≤ ‖A s.1‖ * ‖sigmaAxisProjection I s.1 x‖ := (A s.1).le_opNorm _
    _ ≤ K * ‖x‖ := mul_le_mul (hA s.1) (sigmaAxisProjection_norm_apply_le I s.1 x)
      (norm_nonneg _) hK

omit [Fintype D] [∀ d, Fintype (I d)] in
theorem sigmaAxisOperator_inverse_spec (A : ∀ d, (I d → ℝ) →L[ℝ] (I d → ℝ))
    (hA : ∀ d, (A d).IsInvertible) :
    (sigmaAxisOperator A).IsInvertible ∧
      (sigmaAxisOperator A).inverse = sigmaAxisOperator (fun d => (A d).inverse) := by
  have hr : (sigmaAxisOperator A).comp (sigmaAxisOperator (fun d => (A d).inverse)) =
      ContinuousLinearMap.id ℝ ((Σ d, I d) → ℝ) := by
    ext x s
    change A s.1 ((A s.1).inverse (sigmaAxisProjection I s.1 x)) s.2 = x s
    rw [(hA s.1).self_apply_inverse]
    rfl
  have hl : (sigmaAxisOperator (fun d => (A d).inverse)).comp (sigmaAxisOperator A) =
      ContinuousLinearMap.id ℝ ((Σ d, I d) → ℝ) := by
    ext x s
    change (A s.1).inverse (A s.1 (sigmaAxisProjection I s.1 x)) s.2 = x s
    rw [(hA s.1).inverse_apply_self]
    rfl
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hr hl, ContinuousLinearMap.inverse_eq hr hl⟩

theorem sigmaAxisOperator_inverse_norm_le (A : ∀ d, (I d → ℝ) →L[ℝ] (I d → ℝ))
    (hA : ∀ d, (A d).IsInvertible) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ d, ‖(A d).inverse‖ ≤ K) :
    (sigmaAxisOperator A).IsInvertible ∧ ‖(sigmaAxisOperator A).inverse‖ ≤ K := by
  obtain ⟨hi, he⟩ := sigmaAxisOperator_inverse_spec A hA
  refine ⟨hi, ?_⟩
  rw [he]
  exact sigmaAxisOperator_norm_le _ hK hbound

end Erdos3

end

end OAI

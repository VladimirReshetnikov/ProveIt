import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Pi

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] (I : D → Type*) [∀ d, Fintype (I d)]

noncomputable def sigmaAxisCoordinates : ((Σ d, I d) → ℝ) ≃L[ℝ] (∀ d, I d → ℝ) where
  toLinearEquiv :=
    { toFun := fun x d i => x ⟨d, i⟩
      invFun := fun x s => x s.1 s.2
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def sigmaAxisProjection (d : D) : ((Σ d, I d) → ℝ) →L[ℝ] (I d → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj ⟨d, i⟩)

omit [Fintype D] [∀ d, Fintype (I d)] in
theorem sigmaAxisProjection_apply (d : D) (x : (Σ d, I d) → ℝ) (i : I d) :
    sigmaAxisProjection I d x i = x ⟨d, i⟩ := rfl

theorem sigmaAxisProjection_norm_apply_le (d : D) (x : (Σ d, I d) → ℝ) :
    ‖sigmaAxisProjection I d x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  exact norm_le_pi_norm x ⟨d, i⟩

theorem sigmaAxisProjection_norm_le_one (d : D) : ‖sigmaAxisProjection I d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using sigmaAxisProjection_norm_apply_le I d x

theorem sigmaAxisCoordinates_norm_le_one : ‖(sigmaAxisCoordinates I).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro d
  exact sigmaAxisProjection_norm_apply_le I d x

theorem sigmaAxisCoordinates_symm_norm_le_one :
    ‖(sigmaAxisCoordinates I).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro s
  exact (norm_le_pi_norm (x s.1) s.2).trans (norm_le_pi_norm x s.1)

theorem sigmaAxisCoordinates_symm_measurePreserving :
    MeasurePreserving (sigmaAxisCoordinates I).symm volume volume := by
  refine ⟨(sigmaAxisCoordinates I).symm.continuous.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (sigmaAxisCoordinates I).symm.continuous.measurable (MeasurableSet.univ_pi hs)]
  have he : (sigmaAxisCoordinates I).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun d => Set.univ.pi (fun i : I d => s ⟨d, i⟩)) := by
    ext x
    constructor
    · intro hx d _ i _
      exact hx ⟨d, i⟩ (Set.mem_univ _)
    · intro hx t _
      exact hx t.1 (Set.mem_univ _) t.2 (Set.mem_univ _)
  rw [he, volume_pi_pi]
  simp only [volume_pi_pi, Fintype.prod_sigma]

theorem sigmaAxisCoordinates_measurePreserving :
    MeasurePreserving (sigmaAxisCoordinates I) volume volume :=
  (sigmaAxisCoordinates_symm_measurePreserving I).symm
    (sigmaAxisCoordinates I).symm.toHomeomorph.toMeasurableEquiv

end Erdos3

end

end OAI

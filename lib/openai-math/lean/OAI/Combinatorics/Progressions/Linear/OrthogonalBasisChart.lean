import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

section

namespace Erdos3

open Module

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def orthogonalBasisCoordinates (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) :
    E ≃ₗ[ℝ] W × (Fin n → ℝ) where
  toFun x := (W.orthogonalProjectionOnto x, b.equivFun (Wᗮ.orthogonalProjectionOnto x))
  invFun p := p.1.val + (b.equivFun.symm p.2).val
  left_inv x := by
    change W.starProjection x + (b.equivFun.symm (b.equivFun (Wᗮ.orthogonalProjectionOnto x))).val = x
    rw [LinearEquiv.symm_apply_apply]
    exact W.starProjection_add_starProjection_orthogonal x
  right_inv p := by
    apply Prod.ext
    · change W.orthogonalProjectionOnto (p.1.val + (b.equivFun.symm p.2).val) = p.1
      rw [map_add, W.orthogonalProjectionOnto_apply_of_mem_orthogonal
        (b.equivFun.symm p.2).property, add_zero]
      apply Subtype.ext
      exact W.starProjection_eq_self_iff.mpr p.1.property
    · change b.equivFun (Wᗮ.orthogonalProjectionOnto (p.1.val + (b.equivFun.symm p.2).val)) = p.2
      rw [map_add, W.orthogonalProjectionOnto_orthogonal_apply_eq_zero p.1.property, zero_add]
      have he : Wᗮ.orthogonalProjectionOnto (b.equivFun.symm p.2).val = b.equivFun.symm p.2 := by
        apply Subtype.ext
        exact Wᗮ.starProjection_eq_self_iff.mpr (b.equivFun.symm p.2).property
      rw [he, LinearEquiv.apply_symm_apply]
  map_add' x y := by
    apply Prod.ext <;> simp
  map_smul' a x := by
    apply Prod.ext <;> simp

noncomputable def orthogonalBasisChart (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) :
    E ≃L[ℝ] W × (Fin n → ℝ) := (orthogonalBasisCoordinates W b).toContinuousLinearEquiv

theorem orthogonalBasisChart_apply (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) (x : E) :
    orthogonalBasisChart W b x =
      (W.orthogonalProjectionOnto x, b.equivFun (Wᗮ.orthogonalProjectionOnto x)) := rfl

theorem orthogonalBasisChart_symm_apply (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    (p : W × (Fin n → ℝ)) :
    (orthogonalBasisChart W b).symm p = p.1.val + (b.equivFun.symm p.2).val := rfl

theorem orthogonalBasisChart_norm_le (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖b.equivFun x‖ ≤ C * ‖x‖) (x : E) :
    ‖orthogonalBasisChart W b x‖ ≤ (1 + C) * ‖x‖ := by
  rw [orthogonalBasisChart_apply, Prod.norm_def]
  apply max_le
  · have h := W.norm_orthogonalProjectionOnto_apply_le x
    nlinarith [norm_nonneg x]
  · calc
      _ ≤ C * ‖Wᗮ.orthogonalProjectionOnto x‖ := hb _
      _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_left (Wᗮ.norm_orthogonalProjectionOnto_apply_le x) hC
      _ ≤ _ := by nlinarith [norm_nonneg x]

theorem orthogonalBasisChart_symm_norm_le (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖b.equivFun.symm x‖ ≤ C * ‖x‖)
    (p : W × (Fin n → ℝ)) :
    ‖(orthogonalBasisChart W b).symm p‖ ≤ (1 + C) * ‖p‖ := by
  rw [orthogonalBasisChart_symm_apply]
  calc
    _ ≤ ‖p.1‖ + ‖b.equivFun.symm p.2‖ := norm_add_le _ _
    _ ≤ ‖p.1‖ + C * ‖p.2‖ := by gcongr; exact hb _
    _ ≤ ‖p‖ + C * ‖p‖ := by gcongr; exact norm_fst_le p; exact norm_snd_le p
    _ = _ := by ring

end Erdos3

end

end OAI

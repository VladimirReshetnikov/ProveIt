/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.RealAnnihilatorCorrections

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def realFourCoordinateMap (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ)) :
    (Fin 4 → ℝ ⊗[ℚ] V) →ₗ[ℝ] (J → ℝ) :=
  (realifyCoordinateMap ℓ).comp
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).symm.toLinearMap

theorem real_four_diagonal (x : ℝ ⊗[ℚ] V) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V))
        ((fourDiagonalMap (R := ℚ)).baseChange ℝ x) =
      fourDiagonalMap (R := ℝ) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realFourCoordinateMap_diagonal
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ)) (x : ℝ ⊗[ℚ] V) :
    realFourCoordinateMap ℓ (fourDiagonalMap (R := ℝ) x) =
      realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) x := by
  change realifyCoordinateMap ℓ
    ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).symm _) = _
  rw [← real_four_diagonal, LinearEquiv.symm_apply_apply, realifyCoordinateMap_comp]

theorem realFourCoordinateMap_single
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ)) (k : Fin 4) (x : ℝ ⊗[ℚ] V) :
    realFourCoordinateMap ℓ (LinearMap.single ℝ (fun _ : Fin 4 => ℝ ⊗[ℚ] V) k x) =
      realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) k)) x := by
  change realifyCoordinateMap ℓ
    ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).symm _) = _
  rw [← real_four_single, LinearEquiv.symm_apply_apply, realifyCoordinateMap_comp]

variable [Fintype J]

theorem realFourCoordinateMap_decomposition (C D : Submodule ℚ V)
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ))
    (hℓ : fourBalancedDependent D ≤ LinearMap.ker ℓ)
    (v : Fin 4 → ℝ ⊗[ℚ] V) (hv : v ∈ fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ)) :
    realFourCoordinateMap ℓ v =
      realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) (v 0) +
        realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0))
          (v 0 + v 1 - v 2 - v 3) := by
  have hzero (z) (hz : z ∈ fourBalancedDependent (D.baseChange ℝ)) :
      realFourCoordinateMap ℓ z = 0 := by
    rw [← realification_fourBalancedDependent] at hz
    have hmem := (Submodule.mem_map_equiv _).mp hz
    exact (mem_realified_coordinate_kernel_iff_eq_zero ℓ _).mp
      (Submodule.baseChange_mono ℝ hℓ hmem)
  have h := four_annihilator_decomposition (C.baseChange ℝ) (D.baseChange ℝ)
    (realFourCoordinateMap ℓ) hzero v hv
  simpa only [realFourCoordinateMap_diagonal, realFourCoordinateMap_single,
    fourAlternatingMap_apply] using h

theorem realFourCoordinateMap_shared_decomposition (C D : Submodule ℚ V) (hDC : D ≤ C)
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ))
    (hℓ : fourBalancedDependent D ≤ LinearMap.ker ℓ)
    (c : ℝ ⊗[ℚ] V) (hc : c ∈ C.baseChange ℝ)
    (v : Fin 4 → ℝ ⊗[ℚ] V) (hv : ∀ k, v k ∈ D.baseChange ℝ) :
    realFourCoordinateMap ℓ (fun k => c + v k) =
      realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) c +
        realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0))
          (v 0 + v 1 - v 2 - v 3) := by
  have hmem : (fun k => c + v k) ∈ fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ) := by
    apply (mem_fourCommonModulo _ _ _).mpr
    refine ⟨fun k => (C.baseChange ℝ).add_mem hc
      (Submodule.baseChange_mono ℝ hDC (hv k)), ?_⟩
    intro k
    rw [add_sub_add_left_eq_sub]
    exact (D.baseChange ℝ).sub_mem (hv k) (hv 0)
  have hdiag : D ≤ LinearMap.ker (ℓ.comp (fourDiagonalMap (R := ℚ))) := by
    intro x hx
    exact four_annihilator_common_zero D ℓ (fun z hz => hℓ hz) x hx
  have hz := (mem_realified_coordinate_kernel_iff_eq_zero
    (ℓ.comp (fourDiagonalMap (R := ℚ))) (v 0)).mp
      (Submodule.baseChange_mono ℝ hdiag (hv 0))
  have halt : (c + v 0) + (c + v 1) - (c + v 2) - (c + v 3) =
      v 0 + v 1 - v 2 - v 3 := by abel
  have h := realFourCoordinateMap_decomposition C D ℓ hℓ (fun k => c + v k) hmem
  rw [halt, map_add, hz, add_zero] at h
  exact h

end Erdos3

end

end OAI

import OAI.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix

variable {ι κ V : Type*} [Fintype κ] [AddCommGroup V] [Module ℚ V]

noncomputable def realGeneratorCombination (v : κ → V) (a : κ → ℝ) : ℝ ⊗[ℚ] V :=
  ∑ j, a j ⊗ₜ[ℚ] v j

theorem realGeneratorCombination_mem (U : Submodule ℚ V) (v : κ → V)
    (hv : ∀ j, v j ∈ U) (a : κ → ℝ) : realGeneratorCombination v a ∈ U.baseChange ℝ := by
  classical
  exact Submodule.sum_mem _ (fun j _ => Submodule.tmul_mem_baseChange_of_mem (a j) (hv j))

theorem realGeneratorCombination_coordinates [Fintype ι] (b : Basis ι ℚ V)
    (v : κ → V) (a : κ → ℝ) :
    (b.baseChange ℝ).equivFun (realGeneratorCombination v a) =
      (fun i j => (b.repr (v j) i : ℝ)) *ᵥ a := by
  classical
  funext i
  simp only [realGeneratorCombination, map_sum, Basis.equivFun_apply, Finset.sum_apply,
    Basis.baseChange_repr_tmul, Matrix.mulVec, dotProduct, Rat.smul_def]

theorem realGeneratorCombination_map_coordinates [Fintype ι]
    (φ : V →ₗ[ℚ] (ι → ℚ)) (v : κ → V) (a : κ → ℝ) :
    realRationalCoordinateEquiv (φ.baseChange ℝ (realGeneratorCombination v a)) =
      (fun i j => (φ (v j) i : ℝ)) *ᵥ a := by
  classical
  funext i
  simp only [realGeneratorCombination, map_sum, Finset.sum_apply, LinearMap.baseChange_tmul,
    realRationalCoordinateEquiv_tmul, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end Erdos3

end

end OAI

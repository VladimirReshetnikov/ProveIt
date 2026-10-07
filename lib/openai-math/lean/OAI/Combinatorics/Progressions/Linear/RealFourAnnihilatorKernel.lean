import Mathlib.LinearAlgebra.TensorProduct.Pi
import OAI.Combinatorics.Progressions.Estimates.CommonCoefficientFourAnnihilators

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem mem_realified_coordinate_kernel_iff
    {V J : Type*} [AddCommGroup V] [Module ℚ V] [Fintype J]
    (ℓ : V →ₗ[ℚ] (J → ℚ)) (x : ℝ ⊗[ℚ] V) :
    x ∈ (LinearMap.ker ℓ).baseChange ℝ ↔
      ∀ j, realifyFunctional ((LinearMap.proj j).comp ℓ) x = 0 := by
  have hker : LinearMap.ker ℓ = ⨅ j, LinearMap.ker ((LinearMap.proj j).comp ℓ) := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_iInf, LinearMap.comp_apply, LinearMap.proj_apply]
    exact funext_iff
  rw [hker, real_baseChange_iInf]
  simp only [Submodule.mem_iInf, mem_realified_frequency_kernel_iff]

theorem mem_real_four_annihilator_iff
    {V J : Type*} [AddCommGroup V] [Module ℚ V] [Fintype J]
    (K : Submodule ℚ (Fin 4 → V)) (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ))
    (hker : LinearMap.ker ℓ = K) (v : Fin 4 → ℝ ⊗[ℚ] V) :
    v ∈ (K.baseChange ℝ).map (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).toLinearMap ↔
      ∀ j, realifyFunctional ((LinearMap.proj j).comp ℓ)
        ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).symm v) = 0 := by
  rw [← mem_realified_coordinate_kernel_iff, hker]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).symm
      ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)) x) ∈ K.baseChange ℝ
    rw [LinearEquiv.symm_apply_apply]
    exact hx
  · intro hv
    exact ⟨(TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).symm v, hv,
      (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).apply_symm_apply v⟩

theorem mem_real_petal_annihilator_iff
    {V J : Type*} [AddCommGroup V] [Module ℚ V] [Fintype J]
    (D : Submodule ℚ V) (K : Submodule ℚ (Fin 4 → V))
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ)) (hker : LinearMap.ker ℓ = K)
    (v : ℝ ⊗[ℚ] V) :
    v ∈ (fourPetalSpace D K).baseChange ℝ ↔
      v ∈ D.baseChange ℝ ∧ ∀ j, realifyFunctional
        (((LinearMap.proj j).comp ℓ).comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) v = 0 := by
  rw [fourPetalSpace_eq_inf_ker D K ℓ hker, realification_inf, Submodule.mem_inf,
    mem_realified_coordinate_kernel_iff]
  rfl

end Erdos3

end

end OAI

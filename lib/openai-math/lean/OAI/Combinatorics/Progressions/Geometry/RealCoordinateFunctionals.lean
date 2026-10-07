import OAI.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def realifyCoordinateMap (ℓ : V →ₗ[ℚ] (J → ℚ)) :
    (ℝ ⊗[ℚ] V) →ₗ[ℝ] (J → ℝ) :=
  LinearMap.pi (fun j => realifyFunctional ((LinearMap.proj j).comp ℓ))

noncomputable def coordinateFunctionalMatrix (b : Basis I ℚ V)
    (ℓ : V →ₗ[ℚ] (J → ℚ)) : Matrix J I ℚ := fun j i => ℓ (b i) j

theorem realifyCoordinateMap_tmul (ℓ : V →ₗ[ℚ] (J → ℚ)) (a : ℝ) (v : V) (j : J) :
    realifyCoordinateMap ℓ (a ⊗ₜ[ℚ] v) j = a * (ℓ v j : ℝ) :=
  realifyFunctional_tmul ((LinearMap.proj j).comp ℓ) a v

theorem realifyCoordinateMap_comp {W : Type*} [AddCommGroup W] [Module ℚ W]
    (ℓ : W →ₗ[ℚ] (J → ℚ)) (f : V →ₗ[ℚ] W) (x : ℝ ⊗[ℚ] V) :
    realifyCoordinateMap (ℓ.comp f) x = realifyCoordinateMap ℓ (f.baseChange ℝ x) := by
  funext j
  exact realifyFunctional_comp ((LinearMap.proj j).comp ℓ) f x

theorem realifyCoordinateMap_eq_matrix [Fintype I] (b : Basis I ℚ V)
    (ℓ : V →ₗ[ℚ] (J → ℚ)) (x : ℝ ⊗[ℚ] V) :
    realifyCoordinateMap ℓ x =
      (fun j i => (coordinateFunctionalMatrix b ℓ j i : ℝ)) *ᵥ
        (b.baseChange ℝ).equivFun x := by
  classical
  have h : (realifyCoordinateMap ℓ).comp (b.baseChange ℝ).equivFun.symm.toLinearMap =
      Matrix.mulVecLin (fun j i => (coordinateFunctionalMatrix b ℓ j i : ℝ)) := by
    apply (Pi.basisFun ℝ I).ext
    intro i
    change realifyCoordinateMap ℓ ((b.baseChange ℝ).equivFun.symm (Pi.single i 1)) =
      Matrix.of (fun j k => (coordinateFunctionalMatrix b ℓ j k : ℝ)) *ᵥ Pi.single i 1
    rw [Basis.equivFun_symm_single, Matrix.mulVec_single_one, Basis.baseChange_apply]
    funext j
    rw [realifyCoordinateMap_tmul, one_mul]
    rfl
  have hx := DFunLike.congr_fun h ((b.baseChange ℝ).equivFun x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hx
  exact hx.trans (Matrix.mulVecLin_apply _ _)

theorem realifyCoordinateMap_norm_bound [Fintype I] [Fintype J]
    (b : Basis I ℚ V) (ℓ : V →ₗ[ℚ] (J → ℚ)) {H : ℕ}
    (hℓ : ∀ j i, RationalHeightLE (ℓ (b i) j) H) (x : ℝ ⊗[ℚ] V) :
    ‖realifyCoordinateMap ℓ x‖ ≤
      ((Fintype.card I : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun x‖ := by
  rw [realifyCoordinateMap_eq_matrix b ℓ x]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun j i => (hℓ j i).abs_real_le) _

theorem realifyCoordinateMap_grid [Fintype I] [Fintype J]
    (b : Basis I ℚ V) (ℓ : V →ₗ[ℚ] (J → ℚ)) (l : ℕ) (x : ℝ ⊗[ℚ] V)
    (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    realifyCoordinateMap ℓ x ∈
      realDenominatorGrid (matrixDenominator (coordinateFunctionalMatrix b ℓ) * l) := by
  rw [realifyCoordinateMap_eq_matrix b ℓ x]
  exact real_matrix_denominator_grid (coordinateFunctionalMatrix b ℓ) l _ hx

end Erdos3

end

end OAI

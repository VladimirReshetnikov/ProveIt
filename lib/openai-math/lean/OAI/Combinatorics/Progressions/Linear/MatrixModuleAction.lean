import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def matrixModuleAction {I J W : Type*} [Fintype J]
    [AddCommGroup W] [Module ℝ W] (A : Matrix I J ℝ) : (J → W) →ₗ[ℝ] (I → W) where
  toFun x i := ∑ j, A i j • x j
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm (A i j) r (x j)

theorem matrixModuleAction_apply {I J W : Type*} [Fintype J]
    [AddCommGroup W] [Module ℝ W] (A : Matrix I J ℝ) (x : J → W) (i : I) :
    matrixModuleAction A x i = ∑ j, A i j • x j := rfl

theorem matrixModuleAction_mul {I J K W : Type*} [Fintype J] [Fintype K]
    [AddCommGroup W] [Module ℝ W] (A : Matrix I J ℝ) (B : Matrix J K ℝ) (x : K → W) :
    matrixModuleAction A (matrixModuleAction B x) = matrixModuleAction (A * B) x := by
  funext i
  simp only [matrixModuleAction_apply, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm

theorem matrixModuleAction_image_section {I J W : Type*} [Fintype I] [Fintype J]
    [AddCommGroup W] [Module ℝ W] (A : Matrix I J ℝ) (S : Matrix J I ℝ)
    (hS : A * S * A = A) (x : J → W) :
    matrixModuleAction A (matrixModuleAction S (matrixModuleAction A x)) = matrixModuleAction A x := by
  rw [matrixModuleAction_mul, matrixModuleAction_mul, hS]

end Erdos3

end

end OAI

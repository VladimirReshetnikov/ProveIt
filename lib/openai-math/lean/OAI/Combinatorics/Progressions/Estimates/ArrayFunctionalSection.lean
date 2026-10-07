import OAI.Combinatorics.Progressions.Linear.MatrixModuleAction

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def subspaceArrayFunctional {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℝ) : (I → U) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, ∑ a, frequency i a * (x i).val a
  map_add' x y := by
    simp only [Pi.add_apply, Submodule.coe_add, mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_left_comm]

theorem subspaceArrayFunctional_smul {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℝ) (r : ℝ) (x : I → U) :
    subspaceArrayFunctional U (r • frequency) x = r * subspaceArrayFunctional U frequency x := by
  change (∑ i, ∑ a, (r * frequency i a) * (x i).val a) = r * (∑ i, ∑ a, frequency i a * (x i).val a)
  simp only [Finset.mul_sum, mul_assoc]

theorem subspaceArrayFunctional_matrix {I S J : Type*} [Fintype I] [Fintype S] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (A : Matrix I S ℝ) (frequency : Matrix I J ℝ) (x : S → U) :
    subspaceArrayFunctional U frequency (matrixModuleAction A x) =
      subspaceArrayFunctional U (Aᵀ * frequency) x := by
  change (∑ i, ∑ a, frequency i a * (∑ s, A i s • x s).val a) =
    ∑ s, ∑ a, (∑ i, A i s * frequency i a) * (x s).val a
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ s, ∑ a, frequency i a * (A i s * (x s).val a) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ s, ∑ i, ∑ a, frequency i a * (A i s * (x s).val a) := Finset.sum_comm
    _ = ∑ s, ∑ a, ∑ i, frequency i a * (A i s * (x s).val a) := by
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = _ := by simp only [mul_left_comm, mul_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem subspaceArrayFunctional_factor_section {I S J : Type*} [Fintype I] [Fintype S] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℝ) (T : Matrix I S ℝ)
    (hT : E * T * E = E) (frequency : Matrix I J ℝ)
    (M : (S → U) →ₗ[ℝ] ℝ)
    (hfactor : ∀ x, subspaceArrayFunctional U frequency x = M (matrixModuleAction E x))
    (x : I → U) :
    subspaceArrayFunctional U frequency x =
      subspaceArrayFunctional U (Tᵀ * frequency) (matrixModuleAction E x) := by
  rw [← subspaceArrayFunctional_matrix U T frequency]
  rw [hfactor, hfactor, matrixModuleAction_image_section E T hT]

end Erdos3

end

end OAI

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Kernel bases for systems with vector-space-valued unknowns

Generic scalar-extension algebra for `odg:thm:linear`. A basis of the
scalar kernel parametrizes solutions with coefficients in any vector space.
-/

namespace Surreal.ModuleKernelBasis

open TensorProduct Module

noncomputable section

attribute [local instance] Module.Free.of_divisionRing

variable {K V m n ι : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι]

/-- Tensor extension of a scalar matrix acts by the same finite sums of scalar multiples. -/
theorem tensor_matrix_apply (A : Matrix m n K) (t : V ⊗[K] (n → K)) (j : m) :
    piScalarRight K K V m (AlgebraTensorModule.lTensor K V A.mulVecLin t) j =
      ∑ k, A j k • (piScalarRight K K V n t k) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v x =>
    simp [Matrix.mulVec, dotProduct, Finset.sum_smul, mul_smul]
  | add a b ha hb => simp only [map_add, Pi.add_apply, smul_add, Finset.sum_add_distrib, ha, hb]

/-- Coefficients in a kernel basis correspond to the tensor-extended kernel. -/
def coordinatesEquiv (A : Matrix m n K) (b : Basis ι K (LinearMap.ker A.mulVecLin)) :
    (ι → V) ≃ₗ[K] LinearMap.ker (AlgebraTensorModule.lTensor K V A.mulVecLin) :=
  (Finsupp.linearEquivFunOnFinite K V ι).symm ≪≫ₗ
    (TensorProduct.equivFinsuppOfBasisRight b).symm ≪≫ₗ
    LinearMap.tensorKerEquiv K V A.mulVecLin

omit [Fintype m] [DecidableEq m] in
/-- The tensor parametrization has the expected coordinate formula. -/
theorem coordinatesEquiv_apply (A : Matrix m n K)
    (b : Basis ι K (LinearMap.ker A.mulVecLin)) (h : ι → V) (j : n) :
    piScalarRight K K V n (coordinatesEquiv A b h).val j = ∑ i, (b i).val j • h i := by
  simp [coordinatesEquiv, TensorProduct.equivFinsuppOfBasisRight_symm_apply,
    Finsupp.sum_fintype]

/-- Every vector-space-valued kernel vector has a unique expansion in any scalar kernel basis. -/
theorem existsUnique_kernel_coordinates (A : Matrix m n K)
    (b : Basis ι K (LinearMap.ker A.mulVecLin)) (x : n → V)
    (hx : ∀ j, ∑ k, A j k • x k = 0) :
    ∃! h : ι → V, ∀ j, x j = ∑ i, (b i).val j • h i := by
  let t := (piScalarRight K K V n).symm x
  have ht : t ∈ LinearMap.ker (AlgebraTensorModule.lTensor K V A.mulVecLin) := by
    apply (piScalarRight K K V m).injective
    ext j
    simpa only [tensor_matrix_apply, t, LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply]
      using hx j
  let h := (coordinatesEquiv A b).symm ⟨t, ht⟩
  have he : ∀ j, x j = ∑ i, (b i).val j • h i := by
    intro j
    rw [← coordinatesEquiv_apply]
    simp only [h, LinearEquiv.apply_symm_apply, t, LinearEquiv.apply_symm_apply]
  refine ⟨h, he, ?_⟩
  intro h' hh'
  apply (coordinatesEquiv A b).injective
  apply Subtype.ext
  apply (piScalarRight K K V n).injective
  funext j
  rw [coordinatesEquiv_apply, coordinatesEquiv_apply, ← hh' j, ← he j]

/-- Conversely, every expansion with vector-space coefficients solves the scalar system. -/
theorem kernel_coordinates_solve (A : Matrix m n K)
    (b : Basis ι K (LinearMap.ker A.mulVecLin)) (h : ι → V) (j : m) :
    ∑ k, A j k • (∑ i, (b i).val k • h i) = 0 := by
  simp_rw [← coordinatesEquiv_apply]
  rw [← tensor_matrix_apply]
  have he := (coordinatesEquiv A b h).property
  change AlgebraTensorModule.lTensor K V A.mulVecLin _ = 0 at he
  rw [he, map_zero, Pi.zero_apply]

/-- An injective scalar matrix has no nonzero vector-space-valued kernel vectors. -/
theorem eq_zero_of_injective (A : Matrix m n K) (hA : Function.Injective A.mulVecLin)
    (x : n → V) (hx : ∀ j, ∑ k, A j k • x k = 0) : x = 0 := by
  let t := (piScalarRight K K V n).symm x
  have ht : AlgebraTensorModule.lTensor K V A.mulVecLin t = 0 := by
    apply (piScalarRight K K V m).injective
    ext j
    simpa only [tensor_matrix_apply, t, LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply]
      using hx j
  have hi := Module.Flat.lTensor_preserves_injective_linearMap (M := V) A.mulVecLin hA
  have hz : t = 0 := hi (by rw [map_zero]; exact ht)
  have := congrArg (piScalarRight K K V n) hz
  simpa only [t, LinearEquiv.apply_symm_apply, map_zero] using this

end
end Surreal.ModuleKernelBasis

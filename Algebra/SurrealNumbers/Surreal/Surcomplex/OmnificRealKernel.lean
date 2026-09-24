import Surreal.Surcomplex.OmnificDecomposableFibers
import Surreal.Foundations.OmnificPurelyInfiniteCoefficients

/-!
# Real kernels of complex forms on purely infinite omnific vectors

The real-kernel basis clause of `odg:thm:decomposable` (a). A complex equation
on real unknowns is its pair of real and imaginary equations, so the kernel
is taken over the reals even when the original coefficient matrix is complex.
-/

universe u
namespace Surreal.Surcomplex

open Foundations Module

noncomputable section

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- The real system obtained by separating the real and imaginary rows. -/
def realKernelMatrix {m n : Type*} (A : Matrix m n ℂ) : Matrix (m ⊕ m) n ℝ :=
  Sum.elim (fun j k => (A j k).re) (fun j k => (A j k).im)

/-- The real row kernel is exactly the common kernel of the original complex forms on real vectors. -/
theorem realKernelMatrix_mem_ker_iff {m n : Type*} [Fintype n]
    (A : Matrix m n ℂ) (v : n → ℝ) :
    v ∈ LinearMap.ker (realKernelMatrix A).mulVecLin ↔
      ∀ j, ∑ k, A j k * (v k : ℂ) = 0 := by
  rw [LinearMap.mem_ker, funext_iff]
  change (∀ j, ∑ k, realKernelMatrix A j k * v k = 0) ↔ _
  constructor
  · intro hv j
    apply Complex.ext
    · simpa [realKernelMatrix] using hv (Sum.inl j)
    · simpa [realKernelMatrix] using hv (Sum.inr j)
  · intro hv j
    cases j with
    | inl j => simpa [realKernelMatrix] using congrArg Complex.re (hv j)
    | inr j => simpa [realKernelMatrix] using congrArg Complex.im (hv j)

/-- The ambient value of a purely infinite omnific integer, as an additive homomorphism. -/
def purelyInfiniteValue : SignSequence.omnificPurelyInfiniteIdeal.{u} →+
    SignSequence.{u} :=
  SignSequence.omnificToSurreal.toAddMonoidHom.comp
    SignSequence.omnificPurelyInfiniteIdeal.subtype.toAddMonoidHom

/-- The real coordinate of a complex linear form on a real purely infinite vector. -/
theorem omnific_complex_linear_re {n : Type*} [Fintype n] (a : n → ℂ)
    (v : n → SignSequence.omnificPurelyInfiniteIdeal.{u}) :
    (∑ k, a k • omnificSupportInclusion (v k).val).val.re =
      purelyInfiniteValue (∑ k, (a k).re • v k) := by
  change QuadraticAlgebra.reₗ (-1) 0
    (nonnegativeSupportSubring.subtype (∑ k, a k • omnificSupportInclusion (v k).val)) = _
  rw [map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  change _ = SignSequence.omnificToSurreal (((a k).re • v k).val)
  rw [SignSequence.omnificPurelyInfinite_real_smul]
  change (ofComplex (a k) * ofReal (SignSequence.omnificToSurreal (v k).val)).re = _
  simp

/-- The imaginary coordinate of a complex linear form on a real purely infinite vector. -/
theorem omnific_complex_linear_im {n : Type*} [Fintype n] (a : n → ℂ)
    (v : n → SignSequence.omnificPurelyInfiniteIdeal.{u}) :
    (∑ k, a k • omnificSupportInclusion (v k).val).val.im =
      purelyInfiniteValue (∑ k, (a k).im • v k) := by
  change QuadraticAlgebra.imₗ (-1) 0
    (nonnegativeSupportSubring.subtype (∑ k, a k • omnificSupportInclusion (v k).val)) = _
  rw [map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  change _ = SignSequence.omnificToSurreal (((a k).im • v k).val)
  rw [SignSequence.omnificPurelyInfinite_real_smul]
  change (ofComplex (a k) * ofReal (SignSequence.omnificToSurreal (v k).val)).im = _
  simp

/-- The complex homogeneous system on actual real omnific vectors is its real row system. -/
theorem omnific_complex_kernel_iff {m n : Type*} [Fintype n] (A : Matrix m n ℂ)
    (v : n → SignSequence.omnificPurelyInfiniteIdeal.{u}) :
    (∀ j, ∑ k, A j k • omnificSupportInclusion (v k).val = 0) ↔
      ∀ j, ∑ k, realKernelMatrix A j k • v k = 0 := by
  have hi : Function.Injective (purelyInfiniteValue.{u}) :=
    SignSequence.omnificToSurreal_injective.comp Subtype.val_injective
  constructor
  · intro hv j
    cases j with
    | inl j =>
      apply hi
      change purelyInfiniteValue (∑ k, (A j k).re • v k) = _
      rw [map_zero, ← omnific_complex_linear_re (fun k => A j k) v, hv]
      rfl
    | inr j =>
      apply hi
      change purelyInfiniteValue (∑ k, (A j k).im • v k) = _
      rw [map_zero, ← omnific_complex_linear_im (fun k => A j k) v, hv]
      rfl
  · intro hv j
    apply Subtype.ext
    apply Surcomplex.ext
    · have h := hv (Sum.inl j)
      change ∑ k, (A j k).re • v k = 0 at h
      rw [omnific_complex_linear_re, h, map_zero]
      rfl
    · have h := hv (Sum.inr j)
      change ∑ k, (A j k).im • v k = 0 at h
      rw [omnific_complex_linear_im, h, map_zero]
      rfl

/-- Every real kernel basis gives unique purely infinite parameters for the omnific fiber. -/
theorem omnific_complex_kernel_coordinates_iff {m n ι : Type*}
    [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι]
    (A : Matrix m n ℂ) (b : Basis ι ℝ (LinearMap.ker (realKernelMatrix A).mulVecLin))
    (v : n → SignSequence.omnificPurelyInfiniteIdeal.{u}) :
    (∀ j, ∑ k, A j k • omnificSupportInclusion (v k).val = 0) ↔
      ∃! h : ι → SignSequence.omnificPurelyInfiniteIdeal.{u},
        ∀ k, v k = ∑ i, (b i).val k • h i := by
  rw [omnific_complex_kernel_iff]
  constructor
  · exact ModuleKernelBasis.existsUnique_kernel_coordinates (realKernelMatrix A) b v
  · rintro ⟨h, he, _⟩ j
    simp_rw [he]
    exact ModuleKernelBasis.kernel_coordinates_solve (realKernelMatrix A) b h j

/-- A zero real kernel forces all omnific solutions to be ordinary, even for complex factors. -/
theorem omnific_decomposable_real_full_rank {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (β : m → ℂ) (A : Matrix m n ℂ) (e : m → ℕ) (he : ∀ j, e j ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (x : n → SignSequence.OmnificInteger.{u})
    (hx : DecomposableFibers.value β A e (fun k => omnificSupportInclusion (x k)) =
      complexConstants c) (hA : Function.Injective (realKernelMatrix A).mulVecLin) :
    ∃ a : n → ℤ, ∀ k, x k = SignSequence.omnificIntCast (a k) := by
  obtain ⟨a, v, he, _, hv⟩ := (omnific_decomposable_fiber_iff β A e he c hc x).mp hx
  have hz := ModuleKernelBasis.eq_zero_of_injective (realKernelMatrix A) hA v
    ((omnific_complex_kernel_iff A v).mp hv)
  refine ⟨a, fun k => ?_⟩
  simpa only [hz, Pi.zero_apply, ZeroMemClass.coe_zero, add_zero] using he k

/-- A complex homogeneous equation on real omnific vectors holds iff every coefficient vector
belongs to the real kernel. Coefficients are the actual Conway normal-form coefficients. -/
theorem omnific_complex_kernel_coefficients_iff {m n : Type*} [Fintype n]
    (A : Matrix m n ℂ) (v : n → SignSequence.omnificPurelyInfiniteIdeal.{u}) :
    (∀ j, ∑ k, A j k • omnificSupportInclusion (v k).val = 0) ↔
      ∀ a, (fun k => SignSequence.omnificPurelyInfiniteCoeff a (v k)) ∈
        LinearMap.ker (realKernelMatrix A).mulVecLin := by
  rw [omnific_complex_kernel_iff, SignSequence.omnificPurelyInfinite_linear_coeff_iff]
  simp only [LinearMap.mem_ker, funext_iff, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, Pi.zero_apply]

end
end Surreal.Surcomplex

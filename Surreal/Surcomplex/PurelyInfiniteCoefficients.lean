import Surreal.Surcomplex.GaussianOmnificIntegers
import Surreal.Surcomplex.NormalFormDegree
import Surreal.Surcomplex.StrongConstants
import Surreal.Surcomplex.StrongAlgebra

/-!
# Complex linear coefficients on the actual purely infinite ideal

The coefficientwise and kernel-basis clauses of `odg:dec:thm:gaussianfibers`.
All coefficients come from the actual surcomplex Conway normal form.
-/

universe u
namespace Surreal.Surcomplex

open Foundations Module

noncomputable section

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- Extract an actual Conway coefficient as a complex linear functional on the infinite ideal. -/
def complexPurelyInfiniteCoeff (a : SignSequence.{u}) :
    complexPurelyInfiniteSubmodule.{u} →ₗ[ℂ] ℂ where
  toFun v := growthCoeff v.val.val a
  map_add' v w := by
    change (rawNormalFormRingHom (v.val.val + w.val.val)).coeff _ = _
    rw [map_add, _root_.HahnSeries.coeff_add]
    rfl
  map_smul' r v := by
    change (rawNormalFormRingHom (ofComplex r * v.val.val)).coeff _ = _
    rw [map_mul, rawNormalFormRingHom_apply, rawNormalForm_ofComplex,
      _root_.HahnSeries.coeff_single_zero_mul]
    rfl

/-- Vanishing of all actual complex coefficients detects zero in the infinite ideal. -/
theorem complexPurelyInfinite_eq_zero_iff (v : complexPurelyInfiniteSubmodule.{u}) :
    v = 0 ↔ ∀ a, complexPurelyInfiniteCoeff a v = 0 := by
  constructor
  · rintro rfl a
    exact map_zero _
  · intro hv
    apply Subtype.val_injective
    apply Subtype.val_injective
    apply rawNormalForm_injective
    change rawNormalForm v.val.val = rawNormalForm 0
    rw [rawNormalForm_zero]
    ext g
    obtain ⟨a, ha⟩ := SignSequence.toSurreal_surjective (OrderDual.ofDual g)
    have h := hv a
    change (rawNormalForm v.val.val).coeff (OrderDual.toDual (SignSequence.toSurreal a)) = 0 at h
    rw [ha] at h
    exact h

/-- Complex linear equations in the ideal are exactly the same equations at each exponent. -/
theorem complexPurelyInfinite_linear_coeff_iff {m n : Type*} [Fintype n]
    (A : Matrix m n ℂ) (v : n → complexPurelyInfiniteSubmodule.{u}) :
    (∀ j, ∑ k, A j k • v k = 0) ↔
      ∀ a, (fun k => complexPurelyInfiniteCoeff a (v k)) ∈ LinearMap.ker A.mulVecLin := by
  simp only [complexPurelyInfinite_eq_zero_iff, map_sum, map_smul, smul_eq_mul,
    LinearMap.mem_ker, funext_iff, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply]
  exact forall_comm

/-- Equations in the complex support ring agree with equations in its infinite submodule. -/
theorem complexPurelyInfinite_kernel_iff {m n : Type*} [Fintype n]
    (A : Matrix m n ℂ) (v : n → complexPurelyInfiniteSubmodule.{u}) :
    (∀ j, ∑ k, A j k • (v k).val = 0) ↔ ∀ j, ∑ k, A j k • v k = 0 := by
  constructor
  · intro hv j
    apply Subtype.val_injective
    simpa only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero] using hv j
  · intro hv j
    have h := congrArg Subtype.val (hv j)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero] using h

/-- Every complex kernel basis gives unique purely infinite complex coefficients. -/
theorem complexPurelyInfinite_kernel_coordinates_iff {m n ι : Type*}
    [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι]
    (A : Matrix m n ℂ) (b : Basis ι ℂ (LinearMap.ker A.mulVecLin))
    (v : n → complexPurelyInfiniteSubmodule.{u}) :
    (∀ j, ∑ k, A j k • (v k).val = 0) ↔
      ∃! h : ι → complexPurelyInfiniteSubmodule.{u}, ∀ k, v k = ∑ i, (b i).val k • h i := by
  rw [complexPurelyInfinite_kernel_iff]
  constructor
  · exact ModuleKernelBasis.existsUnique_kernel_coordinates A b v
  · rintro ⟨h, he, _⟩ j
    simp_rw [he]
    exact ModuleKernelBasis.kernel_coordinates_solve A b h j

end
end Surreal.Surcomplex

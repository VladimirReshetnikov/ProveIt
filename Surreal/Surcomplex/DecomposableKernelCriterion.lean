import Surreal.Algebra.NonzeroModuleKernel
import Surreal.Surcomplex.OmnificRealKernel
import Surreal.Surcomplex.GaussianDecomposableFibers
import Surreal.Foundations.OmnificConstantRigidity

/-!
# The exact kernel criterion for nonordinary decomposable fibers

Both the real and Gaussian clauses of `odg:dec:cor:converse`. Given one
ordinary point at a nonzero level, a nonordinary point exists exactly when
the relevant scalar kernel is nonzero. The nonzero coefficient-space
witness is the actual Conway monomial omega.
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- The actual purely infinite omnific vector space contains a nonzero vector. -/
theorem exists_nonzero_omnific_purelyInfinite :
    ∃ t : SignSequence.omnificPurelyInfiniteIdeal.{u}, t ≠ 0 := by
  refine ⟨⟨SignSequence.omnificMonomial 1 zero_lt_one,
    SignSequence.omnificMonomial_mem_purelyInfinite 1 zero_lt_one⟩, ?_⟩
  intro h
  exact SignSequence.omnificMonomial_ne_zero 1 zero_lt_one (congrArg Subtype.val h)

/-- The actual purely infinite complex vector space also contains the nonzero real monomial. -/
theorem exists_nonzero_complex_purelyInfinite :
    ∃ t : complexPurelyInfiniteSubmodule.{u}, t ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_nonzero_omnific_purelyInfinite.{u}
  have hc : constantCoeff (omnificSupportInclusion t.val) = 0 := by
    rw [constantCoeff_omnificSupportInclusion]
    have h : SignSequence.omnificConstantCoeff t.val = 0 := t.property
    rw [h, Int.cast_zero]
  refine ⟨⟨omnificSupportInclusion t.val, hc⟩, ?_⟩
  intro h
  have hz : ofReal (SignSequence.omnificToSurreal t.val) = 0 :=
    congrArg (fun x : complexPurelyInfiniteSubmodule => x.val.val) h
  apply ht
  apply Subtype.val_injective
  apply SignSequence.omnificToSurreal_injective
  change SignSequence.omnificToSurreal t.val = SignSequence.omnificToSurreal 0
  rw [map_zero]
  apply ofReal_injective
  rw [map_zero]
  exact hz

/-- A tuple split into ordinary integers and infinite terms is ordinary exactly when its tail is zero. -/
theorem omnific_split_ordinary_iff {n : Type*} (a : n → ℤ)
    (v : n → SignSequence.omnificPurelyInfiniteIdeal.{u}) :
    (∃ b : n → ℤ, ∀ k, SignSequence.omnificIntCast (a k) + (v k).val =
      SignSequence.omnificIntCast (b k)) ↔ v = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    funext k
    apply Subtype.val_injective
    have ha : a k = b k := by
      have h := congrArg SignSequence.omnificConstantCoeff (hb k)
      simpa only [omnific_split_constant, SignSequence.omnificConstantCoeff_intCast] using h
    have h := hb k
    rw [ha, add_eq_left] at h
    exact h
  · rintro rfl
    exact ⟨a, fun k => by simp⟩

/-- Zero constant coefficient for the inclusion of a complex infinite term into the Gaussian ring. -/
@[simp] theorem gaussianConstantCoeff_purelyInfinite (v : complexPurelyInfiniteSubmodule.{u}) :
    gaussianOmnificConstantCoeff (complexPurelyInfiniteToGaussian v) = 0 := by
  apply GaussianInt.toComplex_injective
  rw [gaussianOmnificConstantCoeff_toComplex, map_zero]
  exact complexPurelyInfinite_constant_zero v

/-- The same exact ordinary-tail test for Gaussian tuples. -/
theorem gaussian_split_ordinary_iff {n : Type*} (a : n → GaussianInt)
    (v : n → complexPurelyInfiniteSubmodule.{u}) :
    (∃ b : n → GaussianInt, ∀ k, gaussianOmnificConstants (a k) +
      complexPurelyInfiniteToGaussian (v k) = gaussianOmnificConstants (b k)) ↔ v = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    funext k
    apply Subtype.val_injective
    have ha : a k = b k := by
      have h := congrArg gaussianOmnificConstantCoeff (hb k)
      simpa only [map_add, gaussianOmnificConstantCoeff_constants,
        gaussianConstantCoeff_purelyInfinite, add_zero] using h
    have h := hb k
    rw [ha, add_eq_left] at h
    exact congrArg (fun z : GaussianOmnificInteger => z.val) h
  · rintro rfl
    refine ⟨a, fun k => Subtype.ext ?_⟩
    change complexConstants (GaussianInt.toComplex (a k)) + 0 =
      complexConstants (GaussianInt.toComplex (a k))
    exact add_zero _

/-- Given an ordinary integer point, a nonordinary omnific point exists iff the real kernel is nonzero. -/
theorem omnific_decomposable_nonordinary_iff {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (β : m → ℂ) (A : Matrix m n ℂ) (e : m → ℕ) (he : ∀ j, e j ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (a : n → ℤ)
    (ha : DecomposableFibers.value β A e (fun k => (a k : ℂ)) = c) :
    (∃ x : n → SignSequence.OmnificInteger.{u},
      DecomposableFibers.value β A e (fun k => omnificSupportInclusion (x k)) = complexConstants c ∧
      ¬ ∃ b : n → ℤ, ∀ k, x k = SignSequence.omnificIntCast (b k)) ↔
      LinearMap.ker (realKernelMatrix A).mulVecLin ≠ ⊥ := by
  obtain ⟨t, ht⟩ := exists_nonzero_omnific_purelyInfinite.{u}
  rw [← ModuleKernelBasis.exists_nonzero_kernel_iff (realKernelMatrix A) t ht]
  constructor
  · rintro ⟨x, hx, hxn⟩
    obtain ⟨b, v, hv, _, hk⟩ := (omnific_decomposable_fiber_iff β A e he c hc x).mp hx
    refine ⟨v, ?_, (omnific_complex_kernel_iff A v).mp hk⟩
    intro hz
    apply hxn
    exact ⟨b, fun k => by simpa only [hz, Pi.zero_apply, ZeroMemClass.coe_zero, add_zero] using hv k⟩
  · rintro ⟨v, hv, hk⟩
    let x : n → SignSequence.OmnificInteger := fun k =>
      SignSequence.omnificIntCast (a k) + (v k).val
    refine ⟨x, (omnific_decomposable_fiber_iff β A e he c hc x).mpr
      ⟨a, v, fun _ => rfl, ha, (omnific_complex_kernel_iff A v).mpr hk⟩, ?_⟩
    exact fun h => hv ((omnific_split_ordinary_iff a v).mp h)

/-- Given an ordinary Gaussian point, a nonordinary Gaussian omnific point exists iff the complex
kernel is nonzero. -/
theorem gaussian_decomposable_nonordinary_iff {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (β : m → ℂ) (A : Matrix m n ℂ) (e : m → ℕ) (he : ∀ j, e j ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (a : n → GaussianInt)
    (ha : DecomposableFibers.value β A e (fun k => GaussianInt.toComplex (a k)) = c) :
    (∃ x : n → GaussianOmnificInteger.{u},
      DecomposableFibers.value β A e (fun k => (x k).val) = complexConstants c ∧
      ¬ ∃ b : n → GaussianInt, ∀ k, x k = gaussianOmnificConstants (b k)) ↔
      LinearMap.ker A.mulVecLin ≠ ⊥ := by
  obtain ⟨t, ht⟩ := exists_nonzero_complex_purelyInfinite.{u}
  rw [← ModuleKernelBasis.exists_nonzero_kernel_iff A t ht]
  constructor
  · rintro ⟨x, hx, hxn⟩
    obtain ⟨b, v, hv, _, hk⟩ := (gaussianOmnific_decomposable_fiber_iff β A e he c hc x).mp hx
    refine ⟨v, ?_, (complexPurelyInfinite_kernel_iff A v).mp hk⟩
    intro hz
    apply hxn
    refine ⟨b, fun k => Subtype.ext ?_⟩
    simpa only [hz, Pi.zero_apply, ZeroMemClass.coe_zero, add_zero,
      gaussianOmnificConstants_val] using hv k
  · rintro ⟨v, hv, hk⟩
    let x : n → GaussianOmnificInteger := fun k =>
      gaussianOmnificConstants (a k) + complexPurelyInfiniteToGaussian (v k)
    refine ⟨x, (gaussianOmnific_decomposable_fiber_iff β A e he c hc x).mpr
      ⟨a, v, fun _ => rfl, ha, (complexPurelyInfinite_kernel_iff A v).mpr hk⟩, ?_⟩
    exact fun h => hv ((gaussian_split_ordinary_iff a v).mp h)

end
end Surreal.Surcomplex

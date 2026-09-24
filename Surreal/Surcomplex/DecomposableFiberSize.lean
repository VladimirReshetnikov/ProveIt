import Surreal.Algebra.KernelLines
import Surreal.Surcomplex.PurelyInfiniteSize

/-!
# Injective lines and proper-class-sized decomposable fibers

The paragraph following `odg:dec:cor:converse`. Each nonzero kernel
direction embeds the entire relevant infinite ideal into the fiber over a
fixed ordinary solution. Thus the actual fiber is not small in the lower
universe, the repository's precise meaning of the proper-class assertion.
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- The line through an ordinary omnific tuple in a real direction. -/
def omnificKernelLine {n : Type*} (a : n → ℤ) (v : n → ℝ)
    (t : SignSequence.omnificPurelyInfiniteIdeal.{u}) : n → SignSequence.OmnificInteger.{u} :=
  fun k => SignSequence.omnificIntCast (a k) + (v k • t).val

/-- Every nonzero real direction gives an injective line of actual omnific tuples. -/
theorem omnificKernelLine_injective {n : Type*} (a : n → ℤ) (v : n → ℝ) (hv : v ≠ 0) :
    Function.Injective (omnificKernelLine.{u} a v) := by
  intro s t h
  apply ModuleKernelBasis.direction_injective v hv
  funext k
  apply Subtype.val_injective
  exact add_left_cancel (congrFun h k)

/-- The actual solution fiber with specified ordinary integer constant tuple. -/
def OmnificDecomposableFiber {m n : Type*} [Fintype m] [Fintype n]
    (β : m → ℂ) (A : Matrix m n ℂ) (e : m → ℕ) (c : ℂ) (a : n → ℤ) :=
  {x : n → SignSequence.OmnificInteger.{u} //
    DecomposableFibers.value β A e (fun k => omnificSupportInclusion (x k)) = complexConstants c ∧
    ∀ k, SignSequence.omnificConstantCoeff (x k) = a k}

/-- Every nonzero real kernel direction embeds the whole infinite ideal in its ordinary fiber. -/
def omnificDecomposableFiberEmbedding {m n : Type*} [Fintype m] [Fintype n]
    (β : m → ℂ) (A : Matrix m n ℂ) (e : m → ℕ) (he : ∀ j, e j ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (a : n → ℤ)
    (ha : DecomposableFibers.value β A e (fun k => (a k : ℂ)) = c)
    (v : n → ℝ) (hv : v ∈ LinearMap.ker (realKernelMatrix A).mulVecLin) (hvn : v ≠ 0) :
    SignSequence.omnificPurelyInfiniteIdeal.{u} ↪ OmnificDecomposableFiber.{u} β A e c a where
  toFun t := ⟨omnificKernelLine a v t,
    (omnific_decomposable_fiber_iff β A e he c hc _).mpr
      ⟨a, fun k => v k • t, fun _ => rfl, ha,
        (omnific_complex_kernel_iff A _).mpr
          (ModuleKernelBasis.kernel_smul_vector (realKernelMatrix A) v hv t)⟩,
    fun k => omnific_split_constant (a k) (v k • t)⟩
  inj' := fun _ _ h => omnificKernelLine_injective a v hvn (congrArg Subtype.val h)

/-- With a nonzero real kernel, the fiber above every ordinary point is not lower-universe-small. -/
theorem omnificDecomposableFiber_not_small {m n : Type*} [Fintype m] [Fintype n]
    (β : m → ℂ) (A : Matrix m n ℂ) (e : m → ℕ) (he : ∀ j, e j ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (a : n → ℤ)
    (ha : DecomposableFibers.value β A e (fun k => (a k : ℂ)) = c)
    (hA : LinearMap.ker (realKernelMatrix A).mulVecLin ≠ ⊥) :
    ¬ Small.{u} (OmnificDecomposableFiber.{u} β A e c a) := by
  intro hs
  letI := hs
  obtain ⟨v, hv, hvn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  exact omnificPurelyInfinite_not_small (small_of_injective
    (omnificDecomposableFiberEmbedding β A e he c hc a ha v hv hvn).injective)

/-- The line through an ordinary Gaussian tuple in a complex direction. -/
def gaussianKernelLine {n : Type*} (a : n → GaussianInt) (v : n → ℂ)
    (t : complexPurelyInfiniteSubmodule.{u}) : n → GaussianOmnificInteger.{u} :=
  fun k => gaussianOmnificConstants (a k) + complexPurelyInfiniteToGaussian (v k • t)

/-- Every nonzero complex direction gives an injective line of Gaussian omnific tuples. -/
theorem gaussianKernelLine_injective {n : Type*} (a : n → GaussianInt) (v : n → ℂ) (hv : v ≠ 0) :
    Function.Injective (gaussianKernelLine.{u} a v) := by
  intro s t h
  apply ModuleKernelBasis.direction_injective v hv
  funext k
  apply Subtype.val_injective
  have he : gaussianOmnificConstants (a k) + complexPurelyInfiniteToGaussian (v k • s) =
      gaussianOmnificConstants (a k) + complexPurelyInfiniteToGaussian (v k • t) := congrFun h k
  exact congrArg (fun x : GaussianOmnificInteger => x.val) (add_left_cancel he)

/-- The actual Gaussian solution fiber with a specified ordinary Gaussian constant tuple. -/
def GaussianDecomposableFiber {m n : Type*} [Fintype m] [Fintype n]
    (β : m → ℂ) (A : Matrix m n ℂ) (e : m → ℕ) (c : ℂ) (a : n → GaussianInt) :=
  {x : n → GaussianOmnificInteger.{u} //
    DecomposableFibers.value β A e (fun k => (x k).val) = complexConstants c ∧
    ∀ k, gaussianOmnificConstantCoeff (x k) = a k}

/-- Every nonzero complex kernel direction embeds the complex infinite ideal in its Gaussian fiber. -/
def gaussianDecomposableFiberEmbedding {m n : Type*} [Fintype m] [Fintype n]
    (β : m → ℂ) (A : Matrix m n ℂ) (e : m → ℕ) (he : ∀ j, e j ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (a : n → GaussianInt)
    (ha : DecomposableFibers.value β A e (fun k => GaussianInt.toComplex (a k)) = c)
    (v : n → ℂ) (hv : v ∈ LinearMap.ker A.mulVecLin) (hvn : v ≠ 0) :
    complexPurelyInfiniteSubmodule.{u} ↪ GaussianDecomposableFiber.{u} β A e c a where
  toFun t := ⟨gaussianKernelLine a v t,
    (gaussianOmnific_decomposable_fiber_iff β A e he c hc _).mpr
      ⟨a, fun k => v k • t, fun _ => rfl, ha,
        (complexPurelyInfinite_kernel_iff A _).mpr (ModuleKernelBasis.kernel_smul_vector A v hv t)⟩,
    fun k => by
      change gaussianOmnificConstantCoeff (gaussianOmnificConstants (a k) +
        complexPurelyInfiniteToGaussian (v k • t)) = a k
      rw [map_add, gaussianOmnificConstantCoeff_constants, gaussianConstantCoeff_purelyInfinite,
        add_zero]⟩
  inj' := fun _ _ h => gaussianKernelLine_injective a v hvn (congrArg Subtype.val h)

/-- With a nonzero complex kernel, every ordinary Gaussian fiber is not lower-universe-small. -/
theorem gaussianDecomposableFiber_not_small {m n : Type*} [Fintype m] [Fintype n]
    (β : m → ℂ) (A : Matrix m n ℂ) (e : m → ℕ) (he : ∀ j, e j ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (a : n → GaussianInt)
    (ha : DecomposableFibers.value β A e (fun k => GaussianInt.toComplex (a k)) = c)
    (hA : LinearMap.ker A.mulVecLin ≠ ⊥) :
    ¬ Small.{u} (GaussianDecomposableFiber.{u} β A e c a) := by
  intro hs
  letI := hs
  obtain ⟨v, hv, hvn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  exact complexPurelyInfinite_not_small (small_of_injective
    (gaussianDecomposableFiberEmbedding β A e he c hc a ha v hv hvn).injective)

end
end Surreal.Surcomplex

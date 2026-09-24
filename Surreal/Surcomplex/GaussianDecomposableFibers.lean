import Surreal.Surcomplex.PurelyInfiniteCoefficients

/-!
# Exact fibers of decomposable equations over Gaussian omnific integers

Completes `odg:dec:thm:gaussianfibers` and `odg:dec:eq:gaussianfiber`.
Solutions are ordinary Gaussian points plus purely infinite complex kernel
vectors, parametrized uniquely in any complex kernel basis. Coefficientwise
kernel membership, disjointness of ordinary fibers and full-rank rigidity
are all on the actual surcomplex support ring.
-/

universe u
namespace Surreal.Surcomplex

noncomputable section

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- The exact Gaussian omnific fiber at a nonzero complex level. -/
theorem gaussianOmnific_decomposable_fiber_iff {m n : Type*} [Fintype m] [Fintype n]
    (β : m → ℂ) (A : Matrix m n ℂ) (e : m → ℕ) (he : ∀ j, e j ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (x : n → GaussianOmnificInteger.{u}) :
    DecomposableFibers.value β A e (fun k => (x k).val) = complexConstants c ↔
      ∃ (a : n → GaussianInt) (v : n → complexPurelyInfiniteSubmodule.{u}),
        (∀ k, (x k).val = complexConstants (GaussianInt.toComplex (a k)) + (v k).val) ∧
        DecomposableFibers.value β A e (fun k => GaussianInt.toComplex (a k)) = c ∧
        ∀ j, ∑ k, A j k • (v k).val = 0 := by
  rw [nonnegativeSupport_decomposable_iff β A e he c hc]
  constructor
  · rintro ⟨hx, hk⟩
    let a : n → GaussianInt := fun k => gaussianOmnificConstantCoeff (x k)
    let v : n → complexPurelyInfiniteSubmodule := fun k =>
      ⟨(x k).val - complexConstants (constantCoeff (x k).val), by
        change constantCoeff ((x k).val - complexConstants (constantCoeff (x k).val)) = 0
        rw [map_sub, constantCoeff_complexConstants, sub_self]⟩
    refine ⟨a, v, ?_, ?_, hk⟩
    · intro k
      dsimp only [a, v]
      rw [gaussianOmnificConstantCoeff_toComplex]
      abel
    · simpa only [a, gaussianOmnificConstantCoeff_toComplex] using hx
  · rintro ⟨a, v, hx, ha, hv⟩
    have hct (k : n) : constantCoeff (x k).val = GaussianInt.toComplex (a k) := by
      rw [hx k, map_add, constantCoeff_complexConstants, complexPurelyInfinite_constant_zero,
        add_zero]
    refine ⟨by simpa only [hct] using ha, fun j => ?_⟩
    have hr (k : n) : (x k).val - complexConstants (constantCoeff (x k).val) = (v k).val := by
      rw [hct, hx k, add_sub_cancel_left]
    simpa only [hr] using hv j

/-- Distinct ordinary Gaussian tuples determine disjoint infinite fibers. -/
theorem gaussianOmnific_fibers_disjoint {n : Type*} (a b : n → GaussianInt)
    (v w : n → complexPurelyInfiniteSubmodule.{u})
    (h : ∀ k, complexConstants (GaussianInt.toComplex (a k)) + (v k).val =
      complexConstants (GaussianInt.toComplex (b k)) + (w k).val) : a = b := by
  funext k
  exact gaussianOmnific_split_constant_unique (a k) (b k) (v k) (w k) (h k)

/-- The homogeneous condition in each Gaussian fiber is precisely coefficientwise kernel membership. -/
theorem gaussianOmnific_kernel_coefficients_iff {m n : Type*} [Fintype n]
    (A : Matrix m n ℂ) (v : n → complexPurelyInfiniteSubmodule.{u}) :
    (∀ j, ∑ k, A j k • (v k).val = 0) ↔
      ∀ a, (fun k => complexPurelyInfiniteCoeff a (v k)) ∈ LinearMap.ker A.mulVecLin := by
  rw [complexPurelyInfinite_kernel_iff, complexPurelyInfinite_linear_coeff_iff]

/-- Full complex column rank forces every Gaussian omnific solution to be ordinary Gaussian. -/
theorem gaussianOmnific_decomposable_full_rank {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (β : m → ℂ) (A : Matrix m n ℂ) (e : m → ℕ) (he : ∀ j, e j ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (x : n → GaussianOmnificInteger.{u})
    (hx : DecomposableFibers.value β A e (fun k => (x k).val) = complexConstants c)
    (hA : Function.Injective A.mulVecLin) :
    ∃ a : n → GaussianInt, ∀ k, x k = gaussianOmnificConstants (a k) := by
  have h := nonnegativeSupport_decomposable_full_rank β A e he c hc (fun k => (x k).val) hx hA
  refine ⟨fun k => gaussianOmnificConstantCoeff (x k), fun k => ?_⟩
  apply Subtype.ext
  rw [gaussianOmnificConstants_val, gaussianOmnificConstantCoeff_toComplex]
  exact h k

end
end Surreal.Surcomplex

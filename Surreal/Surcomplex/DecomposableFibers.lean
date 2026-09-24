import Surreal.Algebra.DecomposableFibers
import Surreal.Surcomplex.OmnificUnits

/-!
# Constant products and decomposable equations in the actual complex support ring

Proves `odg:lem:constantproduct` and the full-column-rank clause (b) of
`odg:thm:decomposable`. The exact constant-term fiber criterion is also
available for every tuple in the actual complex nonnegative-support ring.
-/

universe u
namespace Surreal.Surcomplex

noncomputable section

/-- Complex constants act on the actual complex support ring by multiplication. -/
abbrev nonnegativeSupportComplexAlgebra : Algebra ℂ nonnegativeSupportSubring.{u} :=
  complexConstants.toAlgebra

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- Constant extraction is a homomorphism of complex algebras. -/
def constantCoeffAlgHom : nonnegativeSupportSubring.{u} →ₐ[ℂ] ℂ where
  __ := constantCoeff
  commutes' := constantCoeff_complexConstants

/-- Every unit is exactly the inclusion of its nonzero constant coefficient. -/
theorem nonnegativeSupport_unit_eq_constant (z : nonnegativeSupportSubring.{u}) (hz : IsUnit z) :
    z = complexConstants (constantCoeff z) := by
  obtain ⟨c, _, rfl⟩ := (nonnegativeSupport_isUnit_iff z).mp hz
  rw [constantCoeff_complexConstants]

/-- Every factor of a nonzero constant product in the actual complex support ring is constant. -/
theorem nonnegativeSupport_constant_product {m : Type*} [Fintype m]
    (f : m → nonnegativeSupportSubring.{u}) (c : ℂ) (hc : c ≠ 0)
    (hf : ∏ j, f j = complexConstants c) :
    ∀ j, constantCoeff (f j) ≠ 0 ∧ f j = complexConstants (constantCoeff (f j)) :=
  DecomposableFibers.factors_constant constantCoeffAlgHom nonnegativeSupport_unit_eq_constant
    f c hc hf

/-- Exact nonzero constant fibers in the actual complex support ring. -/
theorem nonnegativeSupport_decomposable_iff {m n : Type*} [Fintype m] [Fintype n]
    (β : m → ℂ) (A : Matrix m n ℂ) (e : m → ℕ) (he : ∀ j, e j ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (x : n → nonnegativeSupportSubring.{u}) :
    DecomposableFibers.value β A e x = complexConstants c ↔
      DecomposableFibers.value β A e (fun k => constantCoeff (x k)) = c ∧
      ∀ j, ∑ k, A j k • (x k - complexConstants (constantCoeff (x k))) = 0 :=
  DecomposableFibers.value_eq_iff constantCoeffAlgHom nonnegativeSupport_unit_eq_constant
    β A e he c hc x

/-- Full complex column rank forces every coordinate of a nonzero constant fiber to be constant. -/
theorem nonnegativeSupport_decomposable_full_rank {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (β : m → ℂ) (A : Matrix m n ℂ) (e : m → ℕ) (he : ∀ j, e j ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (x : n → nonnegativeSupportSubring.{u})
    (hx : DecomposableFibers.value β A e x = complexConstants c)
    (hA : Function.Injective A.mulVecLin) :
    ∀ k, x k = complexConstants (constantCoeff (x k)) :=
  DecomposableFibers.coordinates_constant_of_injective constantCoeffAlgHom
    nonnegativeSupport_unit_eq_constant β A e he c hc x hx hA

end
end Surreal.Surcomplex

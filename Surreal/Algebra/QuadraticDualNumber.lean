import Surreal.Algebra.QuadraticResidueAlgebra
import Mathlib.Algebra.DualNumber

/-!
# The double-root quotient is the dual-number algebra

At the collision in `trigonometry:eq:quadalgebra`, the actual quotient by
`X^2` is isomorphic to Mathlib's dual numbers. Its generator is nonzero
and has square zero. The coefficient of that generator remains the
residue functional, even though evaluation at the unique point loses it.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

/-- Send the quotient generator at the collision to the dual-number infinitesimal. -/
def quadraticToDual : quadraticQuotient (0 : R) →ₐ[R] DualNumber R :=
  AdjoinRoot.liftAlgHom (quadraticPolynomial 0) (Algebra.ofId R (DualNumber R))
    DualNumber.eps (by simp [quadraticPolynomial])

@[simp] theorem quadraticToDual_root :
    quadraticToDual (quadraticRoot (0 : R)) = DualNumber.eps := by
  simp [quadraticToDual, quadraticRoot]

variable [Nontrivial R]

@[simp] theorem quadraticToDual_fst (z : quadraticQuotient (0 : R)) :
    (quadraticToDual z).fst = quadraticConstant 0 z := by
  conv_lhs => rw [quadratic_eq_scalar_add_mul_root 0 z]
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, quadraticToDual_root]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

@[simp] theorem quadraticToDual_snd (z : quadraticQuotient (0 : R)) :
    (quadraticToDual z).snd = quadraticResidue 0 z := by
  conv_lhs => rw [quadratic_eq_scalar_add_mul_root 0 z]
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, quadraticToDual_root]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

/-- The collision algebra is literally the dual numbers, with no quotient dimension loss. -/
def quadraticDualEquiv : quadraticQuotient (0 : R) ≃ₐ[R] DualNumber R :=
  AlgEquiv.ofBijective quadraticToDual ⟨by
    intro z w he
    apply quadratic_ext
    · simpa only [quadraticToDual_fst] using congrArg TrivSqZeroExt.fst he
    · simpa only [quadraticToDual_snd] using congrArg TrivSqZeroExt.snd he, by
    intro z
    refine ⟨algebraMap R _ z.fst + algebraMap R _ z.snd * quadraticRoot 0, ?_⟩
    apply TrivSqZeroExt.ext
    · rw [quadraticToDual_fst, quadraticConstant_scalar_add_mul_root]
    · rw [quadraticToDual_snd, quadraticResidue_scalar_add_mul_root]⟩

/-- The nilpotent direction is present as a nonzero vector at the collision. -/
theorem quadraticRoot_zero_ne_zero : quadraticRoot (0 : R) ≠ 0 := by
  intro he
  have h := congrArg (fun z => (quadraticToDual z).snd) he
  simp at h

/-- The collision retains a nonzero square-zero element. -/
theorem quadratic_collision_nilpotent :
    quadraticRoot (0 : R) ≠ 0 ∧ quadraticRoot (0 : R) ^ 2 = 0 := by
  exact ⟨quadraticRoot_zero_ne_zero, by rw [quadraticRoot_sq, map_zero]⟩

end
end Surreal.FinitePolynomial

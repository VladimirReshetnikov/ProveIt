import Surreal.Surcomplex.OmnificMapClassification
import Surreal.Surcomplex.GaussianInfiniteGenerators
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Small modules and operator representations of omnific rings

The actual real and Gaussian instances of `osq:cor:faithful`, and clause
(i) of `osq:prop:matrices`. The operator formulas allow arbitrary dimension
and the zero space. Finite-dimensional Gaussian conjugacy is separate.
-/

universe u v w
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- No small unital module of the real omnific ring has a faithful scalar action. -/
theorem omnific_no_small_faithfulSMul (M : Type v) [AddCommGroup M]
    [Module OmnificInteger.{u} M] [Small.{u} M] : ¬ FaithfulSMul OmnificInteger.{u} M := by
  intro h
  letI := h
  apply omnificPurelyInfiniteIdeal_ne_bot.{u}
  apply le_bot_iff.mp
  intro x hx
  change x = 0
  exact eq_of_smul_eq_smul (fun m : M => by
    rw [omnific_purelyInfinite_smul_small x hx m, _root_.zero_smul])

/-- Any representation on a small vector space is integer constant extraction times the identity. -/
theorem omnific_small_operator_formula (F : Type v) [Field F] (V : Type w)
    [AddCommGroup V] [Module F V] [Small.{u} V]
    (ρ : OmnificInteger.{u} →+* Module.End F V) (x : OmnificInteger.{u}) :
    ρ x = (omnificConstantCoeff x : Module.End F V) := by
  letI : Small.{u} (Module.End F V) := small_of_injective DFunLike.coe_injective
  exact omnific_small_ringHom_eq_constant ρ x

/-- Evaluating the operator formula gives the ordinary integer multiple of every vector. -/
theorem omnific_small_operator_apply (F : Type v) [Field F] (V : Type w)
    [AddCommGroup V] [Module F V] [Small.{u} V]
    (ρ : OmnificInteger.{u} →+* Module.End F V) (x : OmnificInteger.{u}) (v : V) :
    ρ x v = omnificConstantCoeff x • v := by
  rw [omnific_small_operator_formula F V ρ x]
  simp

/-- The finite matrix formula holds in every dimension, including the zero-dimensional case. -/
theorem omnific_small_matrix_formula (F : Type v) [Field F] [Small.{u} F] (n : ℕ)
    (ρ : OmnificInteger.{u} →+* Matrix (Fin n) (Fin n) F) (x : OmnificInteger.{u}) :
    ρ x = (omnificConstantCoeff x : Matrix (Fin n) (Fin n) F) := by
  letI : Small.{u} (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (Small.{u} (Fin n → Fin n → F))
  exact omnific_small_ringHom_eq_constant ρ x

/-- There exists exactly one such real omnific matrix representation. -/
theorem omnific_small_matrix_unique (F : Type v) [Field F] [Small.{u} F] (n : ℕ) :
    ∃! _ρ : OmnificInteger.{u} →+* Matrix (Fin n) (Fin n) F, True := by
  letI : Small.{u} (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (Small.{u} (Fin n → Fin n → F))
  exact omnific_small_ringHom_unique _

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- No small unital Gaussian omnific module has a faithful scalar action. -/
theorem gaussianOmnific_no_small_faithfulSMul (M : Type v) [AddCommGroup M]
    [Module GaussianOmnificInteger.{u} M] [Small.{u} M] :
    ¬ FaithfulSMul GaussianOmnificInteger.{u} M := by
  intro h
  letI := h
  apply gaussianOmnificPurelyInfiniteIdeal_ne_bot.{u}
  apply le_bot_iff.mp
  intro x hx
  change x = 0
  exact eq_of_smul_eq_smul (fun m : M => by
    rw [gaussianOmnific_purelyInfinite_smul_small x hx m, zero_smul])

/-- Every small-space Gaussian representation has the stated operator formula with J squared minus one. -/
theorem gaussianOmnific_small_operator_formula (F : Type v) [Field F] (V : Type w)
    [AddCommGroup V] [Module F V] [Small.{u} V]
    (ρ : GaussianOmnificInteger.{u} →+* Module.End F V) :
    (ρ gaussianOmnificI) ^ 2 = -1 ∧
      ∀ x : GaussianOmnificInteger.{u},
        ρ x = (SignSequence.omnificConstantCoeff (gaussianOmnificRe x) : Module.End F V) +
          (SignSequence.omnificConstantCoeff (gaussianOmnificIm x) : Module.End F V) *
            ρ gaussianOmnificI := by
  letI : Small.{u} (Module.End F V) := small_of_injective DFunLike.coe_injective
  refine ⟨?_, fun x => gaussianOmnific_small_ringHom_coordinates ρ x⟩
  have h := (gaussianOmnificSmallHomRootEquiv (Module.End F V) ρ).property
  rwa [gaussianOmnificSmallHomRootEquiv_value] at h

/-- Conversely, every square root of minus the identity defines a unique small-space representation. -/
def gaussianOmnificSmallOperatorEquiv (F : Type v) [Field F] (V : Type w)
    [AddCommGroup V] [Module F V] [Small.{u} V] :
    (GaussianOmnificInteger.{u} →+* Module.End F V) ≃
      {J : Module.End F V // J ^ 2 = -1} := by
  letI : Small.{u} (Module.End F V) := small_of_injective DFunLike.coe_injective
  exact gaussianOmnificSmallHomRootEquiv (Module.End F V)

end
end Surreal.Surcomplex

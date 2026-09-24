import Surreal.Foundations.OmnificIntegers
import Surreal.Algebra.PolynomialSolutionRetraction
import Surreal.Algebra.PositiveExistentialRetraction

/-!
# Equational transfer between omnific and ordinary integers

The full `odg:thm:transfer` and `odg:eq:existencetransfer`. Coordinatewise
constant extraction retracts each polynomial solution set onto its
ordinary integer solution set. Positive existential formulas in Mathlib's
native ring language have the same truth at ordinary integer parameters.
-/

universe u v w
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Constant extraction fixes the ordinary integer inclusion. -/
theorem omnificConstantCoeff_leftInverse :
    Function.LeftInverse (omnificConstantCoeff.{u}) omnificIntCast :=
  omnificConstantCoeff_intCast

/-- Constant extraction commutes with evaluation of every integer-coefficient polynomial. -/
theorem omnificConstantCoeff_eval {σ : Type v} (p : MvPolynomial σ ℤ)
    (x : σ → OmnificInteger.{u}) :
    omnificConstantCoeff (p.eval₂ omnificIntCast x) =
      p.eval (fun k => omnificConstantCoeff (x k)) := by
  rw [MvPolynomial.hom_eval₂]
  have h : omnificConstantCoeff.comp (omnificIntCast.{u}) = RingHom.id ℤ :=
    RingHom.ext omnificConstantCoeff_intCast
  rw [h]
  rfl

/-- The actual constant-coefficient map on the whole omnific solution set. -/
def omnificSolutionRetraction {ι : Type v} {σ : Type w} (p : ι → MvPolynomial σ ℤ) :
    PolynomialSolutionRetraction.Solutions p (omnificIntCast.{u}) →
      PolynomialSolutionRetraction.Solutions p (RingHom.id ℤ) :=
  PolynomialSolutionRetraction.retract p omnificIntCast omnificConstantCoeff
    omnificConstantCoeff_leftInverse

/-- Every ordinary solution includes as a constant omnific solution. -/
def omnificSolutionSection {ι : Type v} {σ : Type w} (p : ι → MvPolynomial σ ℤ) :
    PolynomialSolutionRetraction.Solutions p (RingHom.id ℤ) →
      PolynomialSolutionRetraction.Solutions p (omnificIntCast.{u}) :=
  PolynomialSolutionRetraction.sectionMap p omnificIntCast

/-- Coordinatewise inclusion is a section of the solution-set retraction. -/
theorem omnificSolutionRetraction_leftInverse {ι : Type v} {σ : Type w}
    (p : ι → MvPolynomial σ ℤ) :
    Function.LeftInverse (omnificSolutionRetraction.{u} p) (omnificSolutionSection p) :=
  PolynomialSolutionRetraction.leftInverse p omnificIntCast omnificConstantCoeff
    omnificConstantCoeff_leftInverse

/-- Every ordinary solution is the constant tuple of an omnific solution. -/
theorem omnificSolutionRetraction_surjective {ι : Type v} {σ : Type w}
    (p : ι → MvPolynomial σ ℤ) : Function.Surjective (omnificSolutionRetraction.{u} p) :=
  (omnificSolutionRetraction_leftInverse p).surjective

/-- A family of integer polynomial equations has an omnific solution iff it has an integer one.
No finiteness assumption on the family or the variable index is required. -/
theorem omnific_polynomial_solutions_iff {ι : Type v} {σ : Type w}
    (p : ι → MvPolynomial σ ℤ) :
    (∃ x : σ → OmnificInteger.{u}, ∀ j, (p j).eval₂ omnificIntCast x = 0) ↔
      ∃ x : σ → ℤ, ∀ j, (p j).eval x = 0 :=
  PolynomialSolutionRetraction.exists_solution_iff p omnificIntCast omnificConstantCoeff
    omnificConstantCoeff_leftInverse

local instance omnificTransferIntegerStructure : FirstOrder.Ring.CompatibleRing ℤ :=
  FirstOrder.Ring.compatibleRingOfRing ℤ

local instance omnificTransferRingStructure : FirstOrder.Ring.CompatibleRing OmnificInteger.{u} :=
  FirstOrder.Ring.compatibleRingOfRing OmnificInteger

/-- Positive existential ring formulas have identical truth over omnific and ordinary integers
when their free parameters and assigned bound variables are ordinary integers. -/
theorem omnific_positiveExistential_iff {α : Type v} {n : ℕ}
    (φ : FirstOrder.Language.ring.BoundedFormula α n) (hφ : Surreal.IsPositiveExistential φ)
    (v : α → ℤ) (xs : Fin n → ℤ) :
    φ.Realize (omnificIntCast.{u} ∘ v) (omnificIntCast ∘ xs) ↔ φ.Realize v xs :=
  hφ.realize_retraction (Surreal.ringLanguageHom omnificIntCast)
    (Surreal.ringLanguageHom omnificConstantCoeff) omnificConstantCoeff_leftInverse v xs

end
end Surreal.Foundations.SignSequence

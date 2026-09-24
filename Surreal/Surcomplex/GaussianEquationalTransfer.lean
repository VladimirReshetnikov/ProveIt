import Surreal.Surcomplex.GaussianSmallTargets
import Surreal.Algebra.PolynomialSolutionRetraction
import Surreal.Algebra.PositiveExistentialRetraction

/-!
# Equational and positive existential transfer for Gaussian omnific integers

The Gaussian consequence following `osq:prop:conservative`. Coordinatewise
constant extraction retracts arbitrary polynomial solution sets onto their
ordinary Gaussian solution sets. Mathlib's native positive existential
ring formulas have the same truth at ordinary Gaussian parameters.
-/

universe u v w
namespace Surreal.Surcomplex
open Foundations

noncomputable section

/-- Constant extraction fixes the ordinary Gaussian integer inclusion. -/
theorem gaussianOmnificConstantCoeff_leftInverse :
    Function.LeftInverse (gaussianOmnificConstantCoeff.{u}) gaussianOmnificConstants :=
  gaussianOmnificConstantCoeff_constants

/-- Constant extraction commutes with evaluation of every Gaussian-coefficient polynomial. -/
theorem gaussianOmnificConstantCoeff_eval {σ : Type v} (p : MvPolynomial σ GaussianInt)
    (x : σ → GaussianOmnificInteger.{u}) :
    gaussianOmnificConstantCoeff.{u} (p.eval₂ gaussianOmnificConstants x) =
      p.eval (fun k => gaussianOmnificConstantCoeff.{u} (x k)) := by
  rw [MvPolynomial.hom_eval₂]
  have h : gaussianOmnificConstantCoeff.comp (gaussianOmnificConstants.{u}) = RingHom.id GaussianInt :=
    RingHom.ext gaussianOmnificConstantCoeff_constants
  rw [h]
  rfl

/-- The actual constant-coefficient map on the whole Gaussian omnific solution set. -/
def gaussianOmnificSolutionRetraction {ι : Type v} {σ : Type w} (p : ι → MvPolynomial σ GaussianInt) :
    PolynomialSolutionRetraction.Solutions p (gaussianOmnificConstants.{u}) →
      PolynomialSolutionRetraction.Solutions p (RingHom.id GaussianInt) :=
  PolynomialSolutionRetraction.retract p gaussianOmnificConstants gaussianOmnificConstantCoeff
    gaussianOmnificConstantCoeff_leftInverse

/-- Every ordinary solution includes as a constant Gaussian omnific solution. -/
def gaussianOmnificSolutionSection {ι : Type v} {σ : Type w} (p : ι → MvPolynomial σ GaussianInt) :
    PolynomialSolutionRetraction.Solutions p (RingHom.id GaussianInt) →
      PolynomialSolutionRetraction.Solutions p (gaussianOmnificConstants.{u}) :=
  PolynomialSolutionRetraction.sectionMap p gaussianOmnificConstants

/-- Coordinatewise inclusion is a section of the solution-set retraction. -/
theorem gaussianOmnificSolutionRetraction_leftInverse {ι : Type v} {σ : Type w}
    (p : ι → MvPolynomial σ GaussianInt) :
    Function.LeftInverse (gaussianOmnificSolutionRetraction.{u} p) (gaussianOmnificSolutionSection p) :=
  PolynomialSolutionRetraction.leftInverse p gaussianOmnificConstants gaussianOmnificConstantCoeff
    gaussianOmnificConstantCoeff_leftInverse

/-- Every ordinary solution is the constant tuple of a Gaussian omnific solution. -/
theorem gaussianOmnificSolutionRetraction_surjective {ι : Type v} {σ : Type w}
    (p : ι → MvPolynomial σ GaussianInt) : Function.Surjective (gaussianOmnificSolutionRetraction.{u} p) :=
  (gaussianOmnificSolutionRetraction_leftInverse p).surjective

/-- A family of Gaussian polynomial equations has a Gaussian omnific solution iff it has an ordinary one.
No finiteness assumption on the family or the variable index is required. -/
theorem gaussianOmnific_polynomial_solutions_iff {ι : Type v} {σ : Type w}
    (p : ι → MvPolynomial σ GaussianInt) :
    (∃ x : σ → GaussianOmnificInteger.{u}, ∀ j, (p j).eval₂ gaussianOmnificConstants x = 0) ↔
      ∃ x : σ → GaussianInt, ∀ j, (p j).eval x = 0 :=
  PolynomialSolutionRetraction.exists_solution_iff p gaussianOmnificConstants gaussianOmnificConstantCoeff
    gaussianOmnificConstantCoeff_leftInverse

local instance gaussianOmnificTransferIntegerStructure : FirstOrder.Ring.CompatibleRing GaussianInt :=
  FirstOrder.Ring.compatibleRingOfRing GaussianInt

local instance gaussianOmnificTransferRingStructure : FirstOrder.Ring.CompatibleRing GaussianOmnificInteger.{u} :=
  FirstOrder.Ring.compatibleRingOfRing GaussianOmnificInteger

/-- Positive existential ring formulas have identical truth over Gaussian omnific and ordinary Gaussian integers
when their free parameters and assigned bound variables are ordinary Gaussian integers. -/
theorem gaussianOmnific_positiveExistential_iff {α : Type v} {n : ℕ}
    (φ : FirstOrder.Language.ring.BoundedFormula α n) (hφ : Surreal.IsPositiveExistential φ)
    (v : α → GaussianInt) (xs : Fin n → GaussianInt) :
    φ.Realize (gaussianOmnificConstants.{u} ∘ v) (gaussianOmnificConstants ∘ xs) ↔ φ.Realize v xs :=
  hφ.realize_retraction (Surreal.ringLanguageHom gaussianOmnificConstants)
    (Surreal.ringLanguageHom gaussianOmnificConstantCoeff.{u}) gaussianOmnificConstantCoeff_leftInverse v xs

end
end Surreal.Surcomplex

import Surreal.Algebra.PolynomialPresentationReflection
import Surreal.Surcomplex.GaussianSmallTargets

/-!
# Small-ring points of actual omnific polynomial presentations

The actual real and Gaussian instances of `osq:thm:presentations`.
Arbitrary relation ideals are allowed. Target rings may be noncommutative;
only the assertion that the reflected presentation is small requires a
small variable type. The native mapped ideal is identified explicitly for
any family of defining relations.
-/

universe u v w
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- The canonical map from a polynomial presentation to its ordinary constant presentation. -/
def omnificPolynomialPresentationReflection (σ : Type v) (I : Ideal (MvPolynomial σ OmnificInteger.{u})) :
    (MvPolynomial σ OmnificInteger.{u} ⧸ I) →+*
      MvPolynomial σ ℤ ⧸ I.map (MvPolynomial.map omnificConstantCoeff) :=
  PolynomialPresentationReflection.reflection omnificConstantCoeff σ I

/-- The canonical presentation reflection is surjective. -/
theorem omnificPolynomialPresentationReflection_surjective
    (σ : Type v) (I : Ideal (MvPolynomial σ OmnificInteger.{u})) :
    Function.Surjective (omnificPolynomialPresentationReflection σ I) :=
  PolynomialPresentationReflection.reflection_surjective omnificConstantCoeff omnificIntCast
    omnificConstantCoeff_intCast σ I

/-- Every small-ring observation of a presented ring is determined by its constant presentation. -/
def omnificPolynomialPresentationSmallHomEquiv
    (σ : Type v) (I : Ideal (MvPolynomial σ OmnificInteger.{u})) (B : Type w)
    [Ring B] [Small.{u} B] :
    ((MvPolynomial σ OmnificInteger.{u} ⧸ I) →+* B) ≃
      ((MvPolynomial σ ℤ ⧸ I.map (MvPolynomial.map omnificConstantCoeff)) →+* B) :=
  PolynomialPresentationReflection.homEquiv omnificConstantCoeff omnificIntCast
    omnificConstantCoeff_intCast σ
    (fun φ a => omnific_small_hom_eq_constant φ.toNonUnitalRingHom a) I

/-- The inverse map is precomposition with the canonical presentation reflection. -/
theorem omnificPolynomialPresentationSmallHomEquiv_symm
    (σ : Type v) (I : Ideal (MvPolynomial σ OmnificInteger.{u})) (B : Type w)
    [Ring B] [Small.{u} B]
    (ψ : (MvPolynomial σ ℤ ⧸ I.map (MvPolynomial.map omnificConstantCoeff)) →+* B) :
    (omnificPolynomialPresentationSmallHomEquiv σ I B).symm ψ =
      ψ.comp (omnificPolynomialPresentationReflection σ I) := rfl

/-- Small variables make the ordinary reflected presentation small, regardless of the relation ideal. -/
theorem omnificPolynomialPresentation_small (σ : Type v) [Small.{u} σ]
    (I : Ideal (MvPolynomial σ OmnificInteger.{u})) :
    Small.{u} (MvPolynomial σ ℤ ⧸ I.map (MvPolynomial.map omnificConstantCoeff)) :=
  PolynomialPresentationReflection.small_reflected_quotient.{u} omnificConstantCoeff σ I

/-- A family of defining relations becomes precisely the family of constant-coefficient relations. -/
theorem omnificPolynomialPresentation_relations (σ : Type v) {E : Type w}
    (f : E → MvPolynomial σ OmnificInteger.{u}) :
    (Ideal.span (Set.range f)).map (MvPolynomial.map omnificConstantCoeff) =
      Ideal.span (Set.range (fun j => MvPolynomial.map omnificConstantCoeff (f j))) :=
  PolynomialPresentationReflection.map_span_range omnificConstantCoeff σ f

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- The canonical map from a polynomial presentation to its ordinary constant presentation. -/
def gaussianOmnificPolynomialPresentationReflection (σ : Type v) (I : Ideal (MvPolynomial σ GaussianOmnificInteger.{u})) :
    (MvPolynomial σ GaussianOmnificInteger.{u} ⧸ I) →+*
      MvPolynomial σ GaussianInt ⧸ I.map (MvPolynomial.map gaussianOmnificConstantCoeff.{u}) :=
  PolynomialPresentationReflection.reflection gaussianOmnificConstantCoeff.{u} σ I

/-- The canonical presentation reflection is surjective. -/
theorem gaussianOmnificPolynomialPresentationReflection_surjective
    (σ : Type v) (I : Ideal (MvPolynomial σ GaussianOmnificInteger.{u})) :
    Function.Surjective (gaussianOmnificPolynomialPresentationReflection σ I) :=
  PolynomialPresentationReflection.reflection_surjective gaussianOmnificConstantCoeff.{u} gaussianOmnificConstants.{u}
    gaussianOmnificConstantCoeff_constants σ I

/-- Every small-ring observation of a presented ring is determined by its constant presentation. -/
def gaussianOmnificPolynomialPresentationSmallHomEquiv
    (σ : Type v) (I : Ideal (MvPolynomial σ GaussianOmnificInteger.{u})) (B : Type w)
    [Ring B] [Small.{u} B] :
    ((MvPolynomial σ GaussianOmnificInteger.{u} ⧸ I) →+* B) ≃
      ((MvPolynomial σ GaussianInt ⧸ I.map (MvPolynomial.map gaussianOmnificConstantCoeff.{u})) →+* B) :=
  PolynomialPresentationReflection.homEquiv gaussianOmnificConstantCoeff.{u} gaussianOmnificConstants.{u}
    gaussianOmnificConstantCoeff_constants σ
    (fun φ a => gaussianOmnific_small_hom_eq_constant φ.toNonUnitalRingHom a) I

/-- The inverse map is precomposition with the canonical presentation reflection. -/
theorem gaussianOmnificPolynomialPresentationSmallHomEquiv_symm
    (σ : Type v) (I : Ideal (MvPolynomial σ GaussianOmnificInteger.{u})) (B : Type w)
    [Ring B] [Small.{u} B]
    (ψ : (MvPolynomial σ GaussianInt ⧸ I.map (MvPolynomial.map gaussianOmnificConstantCoeff.{u})) →+* B) :
    (gaussianOmnificPolynomialPresentationSmallHomEquiv σ I B).symm ψ =
      ψ.comp (gaussianOmnificPolynomialPresentationReflection σ I) := rfl

/-- Small variables make the ordinary reflected presentation small, regardless of the relation ideal. -/
theorem gaussianOmnificPolynomialPresentation_small (σ : Type v) [Small.{u} σ]
    (I : Ideal (MvPolynomial σ GaussianOmnificInteger.{u})) :
    Small.{u} (MvPolynomial σ GaussianInt ⧸ I.map (MvPolynomial.map gaussianOmnificConstantCoeff.{u})) :=
  PolynomialPresentationReflection.small_reflected_quotient.{u} gaussianOmnificConstantCoeff.{u} σ I

/-- A family of defining relations becomes precisely the family of constant-coefficient relations. -/
theorem gaussianOmnificPolynomialPresentation_relations (σ : Type v) {E : Type w}
    (f : E → MvPolynomial σ GaussianOmnificInteger.{u}) :
    (Ideal.span (Set.range f)).map (MvPolynomial.map gaussianOmnificConstantCoeff.{u}) =
      Ideal.span (Set.range (fun j => MvPolynomial.map gaussianOmnificConstantCoeff.{u} (f j))) :=
  PolynomialPresentationReflection.map_span_range gaussianOmnificConstantCoeff.{u} σ f

end
end Surreal.Surcomplex

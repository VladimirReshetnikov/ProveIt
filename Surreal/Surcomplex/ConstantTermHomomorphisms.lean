import Surreal.Algebra.ConstantTermHomomorphisms
import Surreal.Surcomplex.ConstantTermGraph

/-!
# Constant terms under homomorphisms of the actual omnific rings

The actual-carrier instances of `odg:def:thm:homct`, allowing source and
target at different universes. The Gaussian action is uniform on every
input and determined by the image of the ordinary imaginary unit.
-/

universe u v
namespace Surreal

noncomputable section

namespace Foundations.SignSequence

/-- Every actual omnific homomorphism preserves its integer constant coefficient. -/
theorem omnific_hom_constant (φ : OmnificInteger.{u} →+* OmnificInteger.{v})
    (x : OmnificInteger.{u}) : omnificConstantCoeff (φ x) = omnificConstantCoeff x := by
  have hi : Function.Injective omnificIntCast.{v} :=
    (show Function.LeftInverse omnificConstantCoeff.{v} omnificIntCast.{v} from
      omnificConstantCoeff_intCast).injective
  exact ConstantTermGraph.integer_hom_constant omnificConstantCoeff.{u} omnificIntCast.{u}
    omnificConstantCoeff.{v} omnificIntCast.{v} hi
    omnific_constantTermGraph_iff omnific_constantTermGraph_iff φ x

end Foundations.SignSequence
namespace Surcomplex

/-- A Gaussian omnific homomorphism either fixes every constant term or conjugates every one. -/
theorem gaussianOmnific_hom_constant
    (φ : GaussianOmnificInteger.{u} →+* GaussianOmnificInteger.{v}) :
    (φ (gaussianOmnificConstants.{u} Zsqrtd.sqrtd) = gaussianOmnificConstants.{v} Zsqrtd.sqrtd ∧
      ∀ x, gaussianOmnificConstantCoeff (φ x) = gaussianOmnificConstantCoeff x) ∨
    (φ (gaussianOmnificConstants.{u} Zsqrtd.sqrtd) = -gaussianOmnificConstants.{v} Zsqrtd.sqrtd ∧
      ∀ x, gaussianOmnificConstantCoeff (φ x) = star (gaussianOmnificConstantCoeff x)) := by
  have hi : Function.Injective gaussianOmnificConstants.{v} :=
    (show Function.LeftInverse gaussianOmnificConstantCoeff.{v} gaussianOmnificConstants.{v} from
      gaussianOmnificConstantCoeff_constants).injective
  exact ConstantTermGraph.gaussian_hom_constant
    gaussianOmnificConstantCoeff.{u} gaussianOmnificConstants.{u}
    gaussianOmnificConstantCoeff.{v} gaussianOmnificConstants.{v} hi
    gaussianOmnific_constantTermGraph_iff gaussianOmnific_constantTermGraph_iff φ

end Surcomplex
end
end Surreal

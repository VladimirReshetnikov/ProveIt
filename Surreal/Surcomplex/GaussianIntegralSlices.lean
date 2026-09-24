import Surreal.Algebra.CoefficientPullbackIntegrality
import Surreal.Algebra.GaussianIntegrality
import Surreal.Surcomplex.GaussianFractionField

/-!
# Complex constant and support slices of the Gaussian normalization

The actual-field slice clauses of `osq:nm:thm:complexnormal` and
`osq:nm:eq:complexslice`. On the nonnegative-support ring, the complex
constant coefficient is an algebraic integer exactly when the element
is integral over the Gaussian omnific integers.
-/

universe u
namespace Surreal.Surcomplex
noncomputable section

/-- On nonnegative support, Gaussian omnific integrality is exactly integrality of the coefficient. -/
theorem gaussianOmnific_nonnegative_isIntegral_iff (z : nonnegativeSupportSubring.{u}) :
    IsIntegral GaussianOmnificInteger (z : Surcomplex) ↔ IsIntegral ℤ (constantCoeff z) := by
  exact (CoefficientPullback.integralElem_ambient_iff constantCoeff GaussianInt.toComplex
    GaussianInt.toComplex_injective complexConstants constantCoeff_complexConstants
    nonnegativeSupportSubring.subtype Subtype.val_injective z).trans
      (GaussianIntegrality.coefficient_integral_iff _)

/-- The native subring equality for the full actual nonnegative-support slice. -/
theorem gaussianOmnific_integralClosure_support_slice :
    (integralClosure GaussianOmnificInteger Surcomplex.{u}).toSubring.comap
        nonnegativeSupportSubring.subtype =
      (integralClosure ℤ ℂ).toSubring.comap constantCoeff := by
  ext z
  exact gaussianOmnific_nonnegative_isIntegral_iff z

/-- An ordinary complex constant is Gaussian-omnific integral exactly when it is an algebraic integer. -/
theorem gaussianOmnific_ofComplex_isIntegral_iff (z : ℂ) :
    IsIntegral GaussianOmnificInteger.{u} (ofComplex z : Surcomplex.{u}) ↔ IsIntegral ℤ z := by
  have h := gaussianOmnific_nonnegative_isIntegral_iff (complexConstants.{u} z)
  rwa [constantCoeff_complexConstants] at h

/-- The intersection with the ordinary complex constants is the full algebraic-integer ring. -/
theorem gaussianOmnific_integralClosure_complex_slice :
    (integralClosure GaussianOmnificInteger Surcomplex.{u}).toSubring.comap ofComplex =
      (integralClosure ℤ ℂ).toSubring := by
  ext z
  exact gaussianOmnific_ofComplex_isIntegral_iff z

end
end Surreal.Surcomplex

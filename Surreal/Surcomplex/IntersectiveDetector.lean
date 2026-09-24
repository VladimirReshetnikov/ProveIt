import Surreal.Algebra.IntersectiveDetector
import Surreal.Surcomplex.QuadraticIdealDefinition

/-!
# Nonzero constant terms detected on the actual omnific carriers

The actual omnific and Gaussian omnific conclusions of
`odg:def:thm:detector` and `odg:def:eq:detector`. The formula is the literal
two-witness equation a*s = Lambda(t), without a coefficient-map symbol.
-/

universe u
namespace Surreal

noncomputable section

namespace Foundations.SignSequence

/-- The parameter-free detector accepts precisely actual omnific integers with nonzero constant. -/
theorem omnific_detector_iff (a : OmnificInteger.{u}) :
    IntersectivePolynomial.Detects a ↔ omnificConstantCoeff a ≠ 0 := by
  letI : Algebra ℝ nonnegativeSupportSubring.{u} := realConstants.toAlgebra
  let ct : nonnegativeSupportSubring.{u} →ₐ[ℝ] ℝ :=
    { __ := constantCoeff
      commutes' := constantCoeff_realConstants }
  have hz : omnificConstantCoeff a = 0 ↔ constantCoeff a.val = 0 :=
    CoefficientPullback.mem_ker_iff constantCoeff (Int.castRingHom ℝ) Int.cast_injective a
  refine Iff.trans ?_ (not_congr hz).symm
  exact IntersectivePolynomial.integer_pullback_detector_iff ct (Real.sqrt 13)
    (by norm_num [Real.sq_sqrt]) a

end Foundations.SignSequence
namespace Surcomplex

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- The identical formula detects every nonzero actual Gaussian constant term. -/
theorem gaussianOmnific_detector_iff (a : GaussianOmnificInteger.{u}) :
    IntersectivePolynomial.Detects a ↔ gaussianOmnificConstantCoeff a ≠ 0 := by
  have hz : gaussianOmnificConstantCoeff a = 0 ↔ constantCoeff a.val = 0 :=
    CoefficientPullback.mem_ker_iff constantCoeff GaussianInt.toComplex
      GaussianInt.toComplex_injective a
  refine Iff.trans ?_ (not_congr hz).symm
  apply IntersectivePolynomial.gaussian_pullback_detector_iff constantCoeffAlgHom
    GaussianInt.toComplex GaussianInt.toComplex_injective (Real.sqrt 13 : ℂ)
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)

end Surcomplex
end
end Surreal

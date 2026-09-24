import Surreal.Algebra.IntersectiveDetector
import Surreal.HahnSeries.QuadraticIdealDefinition

/-!
# Detecting nonzero constants in coefficient-restricted Hahn rings

The full Hahn-ring assertion in `odg:def:thm:detector`. These are the full
coefficient pullbacks; arbitrary intermediate subrings are not substituted
for them. There are no rank, divisibility, or support-cardinality hypotheses
on the exponent group.
-/

namespace Surreal.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

attribute [local instance] nonpositiveSupportAlgebra

/-- An available square root of thirteen suffices for the integer-constant detector. -/
theorem integerRestricted_detector_iff [CharZero K] (r : K) (hr : r ^ 2 = 13)
    (a : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K)) :
    IntersectivePolynomial.Detects a ↔ nonpositiveConstantCoeff a.val ≠ 0 :=
  IntersectivePolynomial.integer_pullback_detector_iff
    (nonpositiveConstantCoeffAlgHom (Γ := Γ) (K := K)) r hr a

/-- The Gaussian detector for any coefficient field with the required root and embedding. -/
theorem gaussianRestricted_detector_iff (i : GaussianInt →+* K) (hi : Function.Injective i)
    (r : K) (hr : r ^ 2 = 13) (a : coefficientRestrictedSubring (Γ := Γ) i) :
    IntersectivePolynomial.Detects a ↔ nonpositiveConstantCoeff a.val ≠ 0 :=
  IntersectivePolynomial.gaussian_pullback_detector_iff
    (nonpositiveConstantCoeffAlgHom (Γ := Γ) (K := K)) i hi r hr a

/-- The manuscript's real Hahn-ring detector with no additional hypotheses. -/
theorem realRestricted_detector_iff
    (a : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom ℝ)) :
    IntersectivePolynomial.Detects a ↔ nonpositiveConstantCoeff a.val ≠ 0 :=
  integerRestricted_detector_iff (Real.sqrt 13) (by norm_num [Real.sq_sqrt]) a

/-- The manuscript's complex Hahn-ring detector with Gaussian constant coefficients. -/
theorem complexRestricted_detector_iff
    (a : coefficientRestrictedSubring (Γ := Γ) GaussianInt.toComplex) :
    IntersectivePolynomial.Detects a ↔ nonpositiveConstantCoeff a.val ≠ 0 := by
  apply gaussianRestricted_detector_iff GaussianInt.toComplex GaussianInt.toComplex_injective
    (Real.sqrt 13 : ℂ)
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)

end
end Surreal.HahnSeries

import Surreal.Algebra.IntersectivePolynomial
import Surreal.Surcomplex.GaussianOmnificIntegers

/-!
# The intersective polynomial has no actual omnific roots

The actual integer and Gaussian clauses of `odg:def:prop:intersective` (ii).
For the full omnific rings, the existing ordinary constant-term retractions
already suffice to transfer the ordinary root obstruction.
-/

namespace Surreal

open IntersectivePolynomial

universe u

/-- The ordinary integer retraction rules out every actual omnific root of Lambda. -/
theorem Foundations.SignSequence.omnific_intersectivePolynomial_ne_zero
    (x : Foundations.SignSequence.OmnificInteger.{u}) : value x ≠ 0 := by
  intro h
  have he := congrArg Foundations.SignSequence.omnificConstantCoeff h
  rw [map_value, map_zero] at he
  exact integer_value_ne_zero _ he

/-- The Gaussian retraction rules out every actual Gaussian omnific root of Lambda. -/
theorem Surcomplex.gaussianOmnific_intersectivePolynomial_ne_zero
    (x : Surcomplex.GaussianOmnificInteger.{u}) : value x ≠ 0 := by
  intro h
  have he := congrArg Surcomplex.gaussianOmnificConstantCoeff h
  rw [map_value, map_zero] at he
  exact gaussian_value_ne_zero _ he

end Surreal

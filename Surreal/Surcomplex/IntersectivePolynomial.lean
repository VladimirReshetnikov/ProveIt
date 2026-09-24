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

/-- A Gaussian omnific element with zero constant term has no such multiple certificate,
even if both witnesses are allowed to be Gaussian omnific. -/
theorem Surcomplex.gaussianOmnific_no_intersective_certificate_of_constant_zero
    (v : Surcomplex.GaussianOmnificInteger.{u})
    (hv : Surcomplex.gaussianOmnificConstantCoeff v = 0) :
    ¬∃ s t : Surcomplex.GaussianOmnificInteger.{u}, v * s = value t := by
  rintro ⟨s, t, he⟩
  have h := congrArg Surcomplex.gaussianOmnificConstantCoeff he
  rw [map_mul, hv, zero_mul, map_value] at h
  exact gaussian_value_ne_zero _ h.symm

end Surreal

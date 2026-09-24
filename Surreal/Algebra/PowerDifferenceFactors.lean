import Surreal.Algebra.BinaryFormRigidity
import Mathlib.Algebra.Ring.GeomSum

/-!
# Two projective factors of a power difference

The algebraic factor prerequisite for the equal-power clause of `odg:cor:thue`.
A nontrivial d-th root of unity gives the distinct factors X-Y and X-zeta Y.
-/

namespace Surreal.BinaryFormRigidity

open MvPolynomial

/-- The binary difference of equal powers. -/
noncomputable def powerDifference {R : Type*} [CommRing R] (d : ℕ) : MvPolynomial (Fin 2) R :=
  X 0 ^ d - X 1 ^ d

/-- A d-th root of unity supplies a linear factor of the power difference. -/
theorem linearForm_dvd_powerDifference {K : Type*} [Field K] (d : ℕ) (r : K)
    (hr : r ^ d = 1) : linearForm 1 (-r) ∣ powerDifference (R := K) d := by
  have h := sub_dvd_pow_sub_pow (X 0 : MvPolynomial (Fin 2) K) (C r * X 1) d
  simpa only [linearForm, powerDifference, map_one, one_mul, map_neg, neg_mul,
    ← sub_eq_add_neg, mul_pow, ← map_pow, hr, map_one, one_mul] using h

/-- A nontrivial d-th root of unity proves that there are two projectively distinct factors. -/
theorem powerDifference_hasTwoProjectiveFactors {K : Type*} [Field K]
    (d : ℕ) (r : K) (hr : r ^ d = 1) (hn : r ≠ 1) :
    HasTwoProjectiveFactors (powerDifference (R := K) d) := by
  refine ⟨1, -1, 1, -r, ?_, linearForm_dvd_powerDifference d 1 (one_pow d),
    linearForm_dvd_powerDifference d r hr⟩
  intro h
  apply hn
  linear_combination -h

end Surreal.BinaryFormRigidity

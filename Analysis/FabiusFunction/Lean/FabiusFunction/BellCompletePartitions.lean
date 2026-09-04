import FabiusFunction.ReciprocalExponentialGenerating
import FabiusFunction.ExponentialBell

/-!
# Complete Bell polynomials as finite multiplicity sums

The complete exponential Bell polynomial has the explicit expansion

`Bell.complete c n = n! * ∑_{∑ j*m_j=n} ∏_{j=1}^n (c j / j!)^m_j / m_j!`.

Here `weightedPartitions n` is the finite set of multiplicity vectors:
`f j` is the number of parts of size `j`, its support is contained in
`Icc 1 n`, and the sum of the part sizes is `n`.  The product never uses
`c 0`, so no normalization hypothesis on that unused input is necessary.
At `n = 0` the unique empty vector contributes the empty product `1`.

The proof joins two established identities: the recursive construction
`Bell.complete` agrees with `completeBellPolynomial`, and the latter is
the factorially denormalized weighted-partition sum.  No combinatorial
recurrence or formal-exponential coefficient argument is repeated here.

Reciprocal factorials act as rational scalars.  Thus the main formula is
valid in every commutative rational algebra, including rings with zero
divisors and the zero ring.  The normalized formula cancels a factorial
only in `ℚ`; the field corollary merely rewrites the scalars as division.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

noncomputable section

namespace Fabius

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The complete Bell polynomial is the finite sum over all multiplicity
vectors of weight `n`.  Rational scalar actions express division by both
part-size factorials and multiplicity factorials without a field assumption.
The identity includes `n = 0` and imposes no condition on `c 0`. -/
theorem bell_complete_eq_sum_weightedPartitions (c : ℕ → A) (n : ℕ) :
    Bell.complete c n =
      (n.factorial : ℚ) •
        ∑ f ∈ weightedPartitions n, ∏ j ∈ Icc 1 n,
          (((f j).factorial : ℚ)⁻¹) •
            ((((j.factorial : ℚ)⁻¹) • c j) ^ f j) := by
  simpa only [completeBellPolynomial_eq_complete, partitionExpSum, factorialNormalize]
    using completeBellPolynomial_eq_partitionExpSum c n

/-- Dividing a complete Bell polynomial by `n!` gives its explicit
exponential-generating coefficient, for all indices and all zeroth inputs.
Factorial cancellation takes place in `ℚ`, not in the coefficient algebra. -/
theorem inv_factorial_smul_complete_eq_sum_weightedPartitions
    (c : ℕ → A) (n : ℕ) :
    ((n.factorial : ℚ)⁻¹) • Bell.complete c n =
      ∑ f ∈ weightedPartitions n, ∏ j ∈ Icc 1 n,
        (((f j).factorial : ℚ)⁻¹) •
          ((((j.factorial : ℚ)⁻¹) • c j) ^ f j) := by
  rw [bell_complete_eq_sum_weightedPartitions, smul_smul,
    inv_mul_cancel₀ (by positivity : (n.factorial : ℚ) ≠ 0), one_smul]

/-- The familiar division form of the complete Bell multiplicity formula
over a characteristic-zero field, including the empty partition at zero. -/
theorem bell_complete_eq_sum_div_weightedPartitions
    {F : Type*} [Field F] [CharZero F] (c : ℕ → F) (n : ℕ) :
    Bell.complete c n =
      (n.factorial : F) *
        ∑ f ∈ weightedPartitions n, ∏ j ∈ Icc 1 n,
          (c j / (j.factorial : F)) ^ f j / ((f j).factorial : F) := by
  simpa only [Algebra.smul_def, map_inv₀, map_natCast, div_eq_mul_inv, mul_comm]
    using bell_complete_eq_sum_weightedPartitions c n

end Fabius

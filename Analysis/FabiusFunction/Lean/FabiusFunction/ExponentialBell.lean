import FabiusFunction.ExponentialPartition
import FabiusFunction.MomentCumulantAlgebra
import FabiusFunction.SaddleExpansionAlgebra

/-!
# Weighted partitions and exponential coefficients

`Fabius.partitionExpSum` gives a finite, unordered-partition formula for the
coefficients of an exponential, while `Fabius.SaddleExpansion.expCoeff` gives
the same coefficients recursively and supports the formal power-series and
all-orders asymptotic developments.

This module proves that the two constructions are identical over every
commutative `ℚ`-algebra.  The proof is recurrence uniqueness in its cleanest
form: both coefficient functions start at one and obey the same normalized
successor recurrence.  Consequently every theorem proved through the saddle
coefficient engine immediately has a finite weighted-partition expansion—the
coefficient form underlying complete exponential Bell polynomials.  The
partition formula can therefore be used in targets such as polynomial rings
without introducing field hypotheses.  The final theorem applies the same
identity after canonical factorial normalization, giving the weighted-
partition formula for `completeBellPolynomial` itself.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The finite weighted-partition formula and the recursive exponential
coefficient engine define the same coefficient function in every commutative
rational algebra. -/
theorem partitionExpSum_eq_expCoeff
    {R : Type*} [CommRing R] [Algebra ℚ R] (E : ℕ → R) :
    partitionExpSum E = SaddleExpansion.expCoeff E := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · simp
      · rw [partitionExpSum_succ, SaddleExpansion.expCoeff_succ]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih (n - j) (by omega)]

/-- A complete exponential Bell polynomial is the factorially denormalized
weighted-partition sum of the factorially normalized cumulants. -/
theorem completeBellPolynomial_eq_partitionExpSum
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (κ : ℕ → R) (n : ℕ) :
    completeBellPolynomial κ n =
      (n.factorial : ℚ) • partitionExpSum (factorialNormalize κ) n := by
  rw [completeBellPolynomial, factorialDenormalize,
    partitionExpSum_eq_expCoeff]

end Fabius

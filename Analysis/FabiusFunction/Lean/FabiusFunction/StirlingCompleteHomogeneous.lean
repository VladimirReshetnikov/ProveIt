import FabiusFunction.StirlingOrdinaryGF
import FabiusFunction.CompleteHomogeneousBell
import FabiusFunction.CompleteHomogeneousWeakComposition

/-!
# Stirling columns as complete homogeneous symmetric polynomials

For every `k, r ≥ 0`,

`S(k+r,k) = h_r(1,2,...,k)`.

This is `eq:second-complete-symmetric` in `thm:second-ogf` of the canonical
`Combinatorial_Coefficient_Calculus` monograph. The identity is proved over
every commutative semiring: adjoining the variable `k+1` to a complete
homogeneous polynomial gives exactly the Stirling recurrence. The boundary
values agree, so double induction closes the identification without division
or a generating-function cancellation argument.

The existing complete-homogeneous/Bell dictionary then gives

`Bell.complete b r = r! * S(k+r,k)`,

where `b 0 = 0` and `b (m+1) = m! * ∑_{j=1}^k j^(m+1)`.
This form remains valid in positive characteristic and over semirings with
zero divisors. Over a commutative rational algebra, factorial normalization
recovers the usual quotient by `r!`.

## Main results

* `stirlingSecond_add_eq_completeHomogeneousEvalOn`: the identity indexed by
  a column `k` and an offset `r`, with no side conditions.
* `stirlingSecond_eq_completeHomogeneousEvalOn`: the manuscript indexing
  `S(n,k) = h_(n-k)(1,...,k)` under `k ≤ n`.
* `stirlingSecond_add_eq_sum_antidiagonalTuple`: the explicit sum over all
  weak compositions of the offset into `k` nonnegative parts.
* `stirlingColumnOGF_eq_completeHomogeneousGeneratingSeriesOn`: the existing
  Stirling column and complete homogeneous generating series coincide.
* `bellComplete_stirlingSecond_powerSums`: the division-free Bell formula.
* `stirlingSecond_add_eq_factorialNormalize_completeBellPolynomial`: the
  normalized Bell formula over a commutative rational algebra.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

/-- **Stirling columns are complete homogeneous evaluations.**

For every commutative semiring, `S(k+r,k) = h_r(1,...,k)`. Both `k = 0` and
`r = 0` are included, using the standard empty-family and degree-zero
conventions. This is the offset form of `eq:second-complete-symmetric`. -/
theorem stirlingSecond_add_eq_completeHomogeneousEvalOn
    {R : Type*} [CommSemiring R] (k r : ℕ) :
    (Nat.stirlingSecond (k + r) k : R) =
      completeHomogeneousEvalOn (Finset.range k) (fun j => ((j + 1 : ℕ) : R)) r := by
  classical
  induction k generalizing r with
  | zero =>
      cases r <;> simp [completeHomogeneousEvalOn, Nat.stirlingSecond]
  | succ k hk =>
      induction r with
      | zero => simp [completeHomogeneousEvalOn, Nat.stirlingSecond_self]
      | succ r hr =>
          have hrec :
              completeHomogeneousEvalOn (Finset.range (k + 1))
                  (fun j => ((j + 1 : ℕ) : R)) (r + 1) =
                ((k + 1 : ℕ) : R) *
                    completeHomogeneousEvalOn (Finset.range (k + 1))
                      (fun j => ((j + 1 : ℕ) : R)) r +
                  completeHomogeneousEvalOn (Finset.range k)
                    (fun j => ((j + 1 : ℕ) : R)) (r + 1) := by
            simpa only [Finset.range_add_one] using
              completeHomogeneousEvalOn_insert_succ
                (s := Finset.range k) (i := k) (by simp)
                (fun j => ((j + 1 : ℕ) : R)) r
          rw [hrec, ← hr, ← hk (r + 1),
            show k + 1 + (r + 1) = (k + r + 1) + 1 by omega,
            show k + 1 + r = k + r + 1 by omega,
            show k + (r + 1) = k + r + 1 by omega,
            Nat.stirlingSecond_succ_succ, Nat.cast_add, Nat.cast_mul]

/-- **The complete homogeneous coefficient formula in manuscript notation.**

For `k ≤ n`, `S(n,k) = h_(n-k)(1,...,k)` over every commutative semiring.
This is `eq:second-complete-symmetric` in `thm:second-ogf` of
`Combinatorial_Coefficient_Calculus`. -/
theorem stirlingSecond_eq_completeHomogeneousEvalOn
    {R : Type*} [CommSemiring R] (n k : ℕ) (hk : k ≤ n) :
    (Nat.stirlingSecond n k : R) =
      completeHomogeneousEvalOn (Finset.range k)
        (fun j => ((j + 1 : ℕ) : R)) (n - k) := by
  simpa only [show k + (n - k) = n by omega] using
    stirlingSecond_add_eq_completeHomogeneousEvalOn (R := R) k (n - k)

/-- **The explicit weak-composition formula for every Stirling column.**

Each tuple `c : Fin k → ℕ` has total degree `r` and contributes
`1^(c 0) ··· k^(c (k-1))` once. This is the second equality of
`eq:second-complete-symmetric`, with `n = k + r`, over every commutative
semiring and with the empty-family conventions built into the finite sum. -/
theorem stirlingSecond_add_eq_sum_antidiagonalTuple
    {R : Type*} [CommSemiring R] (k r : ℕ) :
    (Nat.stirlingSecond (k + r) k : R) =
      ∑ c ∈ Finset.Nat.antidiagonalTuple k r,
        ∏ i : Fin k, (((i : ℕ) + 1 : ℕ) : R) ^ c i := by
  rw [stirlingSecond_add_eq_completeHomogeneousEvalOn,
    completeHomogeneousEvalOn_range_eq_sum_antidiagonalTuple]

/-- The formal Stirling column series is exactly the complete homogeneous
generating series on the variables `1,...,k`. -/
theorem stirlingColumnOGF_eq_completeHomogeneousGeneratingSeriesOn
    {R : Type*} [CommRing R] (k : ℕ) :
    stirlingColumnOGF R k =
      completeHomogeneousGeneratingSeriesOn (Finset.range k)
        (fun j => ((j + 1 : ℕ) : R)) := by
  ext r
  rw [coeff_stirlingColumnOGF, coeff_completeHomogeneousGeneratingSeriesOn]
  exact stirlingSecond_add_eq_completeHomogeneousEvalOn k r

/-- **A division-free Bell formula for every Stirling column.**

Set `b 0 = 0` and `b (m+1) = m! * ∑_{j=1}^k j^(m+1)`. Then
`Bell.complete b r = r! * S(k+r,k)` over every commutative semiring.
The input is the existing `completeHomogeneousBellInput` specialized to
the variables `1,...,k`; no factorial is assumed invertible. -/
theorem bellComplete_stirlingSecond_powerSums
    {R : Type*} [CommSemiring R] (k r : ℕ) :
    Bell.complete
        (completeHomogeneousBellInput (Finset.range k)
          (fun j => ((j + 1 : ℕ) : R))) r =
      (r.factorial : R) * (Nat.stirlingSecond (k + r) k : R) := by
  rw [bellComplete_completeHomogeneousBellInput,
    ← stirlingSecond_add_eq_completeHomogeneousEvalOn]

/-- Over a commutative rational algebra, a Stirling column is the complete
Bell polynomial of its factorially weighted power sums, divided by `r!`.
Here `factorialNormalize` implements that division by the rational scalar. -/
theorem stirlingSecond_add_eq_factorialNormalize_completeBellPolynomial
    {R : Type*} [CommRing R] [Algebra ℚ R] (k r : ℕ) :
    (Nat.stirlingSecond (k + r) k : R) =
      factorialNormalize
        (completeBellPolynomial
          (completeHomogeneousBellInput (Finset.range k)
            (fun j => ((j + 1 : ℕ) : R)))) r := by
  rw [stirlingSecond_add_eq_completeHomogeneousEvalOn]
  exact completeHomogeneousEvalOn_eq_factorialNormalize_completeBellPolynomial
    (Finset.range k) (fun j => ((j + 1 : ℕ) : R)) r

end Fabius

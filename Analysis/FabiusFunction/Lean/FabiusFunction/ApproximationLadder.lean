import FabiusFunction.ThueMorseApproximation
import FabiusFunction.ThueMorseBlockAlgebra

/-!
# The ladder form of the approximation polynomial

The corpus's `approximationPolynomialInt d` is the `q`-integer product
`∏_{m=1}^{d} [2^m]_X`, obtained by clearing `(1-X)^{d+1}` from the
Thue–Morse block polynomial.  Dividing the block's *ladder*
factorization by the same power gives the closed cyclotomic-free
product form

`A_d = ∏_{i<d} (1 + X^{2^i})^{d-i}`,

a product of self-reciprocal factors with multiplicity decreasing in
the scale — the annihilator form used by the dictionary layer.

* `approximationPolynomialInt_eq_ladder` — the closed product over
  `range (d+1)` (the top factor is trivial);
* `approximationPolynomialInt_eq_ladder'` — the same over `range d`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

open Polynomial

private theorem one_sub_X_ne_zero :
    (1 - Polynomial.X : Polynomial ℤ) ≠ 0 := fun h => by
  simpa using congrArg (Polynomial.eval 0) h

/-- **The ladder form of the approximation polynomial**: dividing the
block's ladder factorization by `(1-X)^{d+1}` leaves a product of
self-reciprocal factors with scale-decreasing multiplicity. -/
theorem approximationPolynomialInt_eq_ladder (d : ℕ) :
    approximationPolynomialInt d =
      ∏ i ∈ range (d + 1),
        ((1 : Polynomial ℤ) + Polynomial.X ^ 2 ^ i) ^ (d - i) := by
  have hcancel : (1 - Polynomial.X : Polynomial ℤ) ^ (d + 1) *
      approximationPolynomialInt d =
      (1 - Polynomial.X : Polynomial ℤ) ^ (d + 1) *
        ∏ i ∈ range (d + 1),
          ((1 : Polynomial ℤ) + Polynomial.X ^ 2 ^ i) ^ (d - i) := by
    rw [one_sub_X_pow_mul_approximationPolynomialInt d,
      thueMorseBlockPolynomial_eq_ladder (d + 1)]
    congr 1
  exact mul_left_cancel₀ (pow_ne_zero _ one_sub_X_ne_zero) hcancel

/-- The ladder form with the trivial top factor dropped. -/
theorem approximationPolynomialInt_eq_ladder' (d : ℕ) :
    approximationPolynomialInt d =
      ∏ i ∈ range d,
        ((1 : Polynomial ℤ) + Polynomial.X ^ 2 ^ i) ^ (d - i) := by
  rw [approximationPolynomialInt_eq_ladder d, Finset.prod_range_succ,
    Nat.sub_self, pow_zero, mul_one]

end Fabius

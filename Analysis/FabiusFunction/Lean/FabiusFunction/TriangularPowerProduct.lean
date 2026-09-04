import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic

/-!
# Triangular exponent sums in a commutative monoid

Two finite-product facts recur throughout the corpus wherever a dyadic
or geometric chain is collapsed: the triangular exponent sum

`∏_{j<K} z^j = z^(K choose 2)`

and its shifted form `∏_{k<m} z^(k+1) = z^((m+1) choose 2)`.  Neither
has anything to do with the Fabius function or the Thue–Morse sequence,
and neither needs more than a commutative monoid, so they live here in a
leaf that imports only Mathlib.  Modules that used to re-derive the
identity inline can adopt these at no rebuild cost to anyone else.

* `prod_range_pow_eq_pow_choose_two`
* `prod_range_pow_succ_eq_pow_choose_two`
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- `∏_{j<K} z^j = z^(K choose 2)` in any commutative monoid. -/
theorem prod_range_pow_eq_pow_choose_two {M : Type*} [CommMonoid M]
    (z : M) (K : ℕ) :
    ∏ j ∈ range K, z ^ j = z ^ K.choose 2 := by
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id,
    Nat.choose_two_right]

/-- The shifted exponent sum: `∏_{k<m} z^(k+1) = z^((m+1) choose 2)`. -/
theorem prod_range_pow_succ_eq_pow_choose_two {M : Type*} [CommMonoid M]
    (z : M) (m : ℕ) :
    ∏ k ∈ range m, z ^ (k + 1) = z ^ (m + 1).choose 2 := by
  rw [← prod_range_pow_eq_pow_choose_two, Finset.prod_range_succ',
    pow_zero, mul_one]

end Fabius

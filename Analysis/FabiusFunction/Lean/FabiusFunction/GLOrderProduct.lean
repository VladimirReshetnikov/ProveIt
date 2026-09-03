import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic

/-!
# The falling product `∏_{i<n} (qⁿ - qⁱ)`, division-free

This module exists to hold one identity, in a place light enough for anything to import:

`∏_{i<n} (qⁿ - qⁱ) = q^{C(n,2)} ∏_{j<n} (q^{j+1} - 1)`.

Over a finite field with `Q` elements the left-hand side is `|GLₙ(F_Q)|`, so the identity exhibits
that order as a power of `Q` times a `q`-factorial-like product.  At `Q = 2` it is
`1, 1, 6, 168, 20160, 9999360, …`.

## Why its own module

The natural homes were both wrong, in opposite directions.  Stated inside the matrix-counting
module, the lemma is unusable by anything that does not want Mathlib's linear algebra: a consumer
that only multiplies powers of two would drag in bases, dimension, quotients and matrix rank.
Stated inside one of the foundational `q`-series modules, it is importable but every edit to it
invalidates a large part of the corpus, which on a shared machine is a real cost for nine lines.

So it lives alone, with an import closure of Mathlib's `Finset` products and `Nat.choose` and
nothing from the corpus at all.

## Generality

`prod_pow_sub_pow_eq_pow_choose_two_mul` holds over an **arbitrary commutative ring** for an
**arbitrary** `q`, with no invertibility, nonvanishing, domain or characteristic hypothesis, and
none is needed: the proof only factors `qⁿ - qⁱ = qⁱ(q^{n-i} - 1)` and reflects the index.  This is
stated explicitly because a general lemma whose hypothesis list is empty is easy to mistake for a
narrow one and re-prove.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **The falling product as a power times a `q`-factorial-like product.**
`∏_{i<n} (qⁿ - qⁱ) = q^{C(n,2)} ∏_{j<n} (q^{j+1} - 1)`.

Over an arbitrary commutative ring, for an arbitrary `q`: there is no invertibility, nonvanishing
or domain hypothesis, and none is needed.  Over a finite field with `Q` elements the left side is
`|GLₙ|`, the number of ordered bases of `F_Q^n`. -/
theorem prod_pow_sub_pow_eq_pow_choose_two_mul {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    ∏ i ∈ range n, (q ^ n - q ^ i) = q ^ n.choose 2 * ∏ j ∈ range n, (q ^ (j + 1) - 1) := by
  have hfactor : ∀ i ∈ range n, q ^ n - q ^ i = q ^ i * (q ^ (n - i) - 1) := by
    intro i hi
    have hi' : i ≤ n := (mem_range.mp hi).le
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hi']
  have hrefl : ∏ i ∈ range n, (q ^ (n - i) - 1) = ∏ j ∈ range n, (q ^ (j + 1) - 1) := by
    rw [← Finset.prod_range_reflect (fun j => q ^ (j + 1) - 1) n]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < n := mem_range.mp hi
    congr 2
    omega
  rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib, hrefl,
    Finset.prod_pow_eq_pow_sum, Finset.sum_range_id, Nat.choose_two_right]

end Fabius

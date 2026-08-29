import FabiusFunction.ThueMorseBooleanCube

/-!
# The bit-position generating identity

The corpus's Boolean-cube master identity `prod_one_add_mul_pow`
weights a dyadic block by the *value* `z^n`.  Its companion weights
each `n` instead by the *sum of its bit positions*

`σ(n) = ∑_{j ∈ bitSupport n} j`,

which is the statistic the `q`-binomial layer grades by.  Over any
commutative semiring,

`∏_{j<N} (1 + y·qʲ) = ∑_{n<2ᴺ} y^{w(n)}·q^{σ(n)}`,

by the same two-step route: expand the product over the Boolean cube,
then reindex subsets of `range N` by the naturals they encode.  Under
that reindexing a subset's cardinality becomes the binary weight of
its code and the sum of its elements becomes `σ` of its code.

Specializing `y ↦ 1` counts the block by `q^σ` alone, and `q ↦ 1`
recovers the corpus's binary-weight enumerator.

* `bitPositionSum` — the statistic `σ`;
* `bitPositionSum_sum_two_pow` — `σ` of an encoded set is the set's
  sum;
* `prod_one_add_mul_pow_bitPositionSum` — **the identity**;
* `prod_one_add_pow_eq_sum_bitPositionSum` — the `y = 1` face.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The sum of the binary positions at which `n` has a one bit. -/
def bitPositionSum (n : ℕ) : ℕ :=
  ∑ j ∈ bitSupport n, j

@[simp] theorem bitPositionSum_zero : bitPositionSum 0 = 0 := by
  simp [bitPositionSum]

/-- The bit-position sum of an encoded finite set is the sum of that
set. -/
@[simp] theorem bitPositionSum_sum_two_pow (T : Finset ℕ) :
    bitPositionSum (∑ j ∈ T, 2 ^ j) = ∑ j ∈ T, j := by
  rw [bitPositionSum, bitSupport_sum_two_pow]

/-- **The bit-position generating identity**: over any commutative
semiring, `∏_{j<N} (1 + y·qʲ) = ∑_{n<2ᴺ} y^{w(n)}·q^{σ(n)}`. -/
theorem prod_one_add_mul_pow_bitPositionSum {R : Type*}
    [CommSemiring R] (y q : R) (N : ℕ) :
    ∏ j ∈ range N, (1 + y * q ^ j) =
      ∑ n ∈ range (2 ^ N),
        y ^ binaryWeight n * q ^ bitPositionSum n := by
  rw [prod_one_add_eq_sum_powerset]
  rw [← sum_powerset_two_pow N
    (fun n => y ^ binaryWeight n * q ^ bitPositionSum n)]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hcard : binaryWeight (∑ j ∈ T, 2 ^ j) = T.card :=
    binaryWeight_sum_two_pow_eq_card T
  have hpos : bitPositionSum (∑ j ∈ T, 2 ^ j) = ∑ j ∈ T, j :=
    bitPositionSum_sum_two_pow T
  rw [hcard, hpos, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum]

/-- The `y = 1` face: the dyadic block graded by the bit-position sum
alone. -/
theorem prod_one_add_pow_eq_sum_bitPositionSum {R : Type*}
    [CommSemiring R] (q : R) (N : ℕ) :
    ∏ j ∈ range N, (1 + q ^ j) =
      ∑ n ∈ range (2 ^ N), q ^ bitPositionSum n := by
  have h := prod_one_add_mul_pow_bitPositionSum (1 : R) q N
  simpa using h

/-- The `q = 1` face: the binary-weight enumerator of a dyadic
block. -/
theorem prod_one_add_eq_sum_binaryWeight {R : Type*} [CommSemiring R]
    (y : R) (N : ℕ) :
    (1 + y) ^ N = ∑ n ∈ range (2 ^ N), y ^ binaryWeight n := by
  have h := prod_one_add_mul_pow_bitPositionSum y (1 : R) N
  simpa using h

end Fabius

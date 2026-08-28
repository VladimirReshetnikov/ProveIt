import FabiusFunction.ThueMorseBitSupport

/-!
# The Boolean cube structure of dyadic blocks

Everything the formula atlas derives from generating products rests on one
combinatorial fact: the dyadic block `{0, …, 2^m - 1}` *is* the Boolean
cube `{0,1}^m`, via binary expansion.  This module isolates that fact in a
maximally reusable form and proves the atlas's master product identity in
full generality.

* `sum_powerset_two_pow` — the **reindexing kernel**: for any function into
  any additive commutative monoid,
  `∑_{T ⊆ range m} f (∑_{j ∈ T} 2^j) = ∑_{n < 2^m} f n`.
* `binaryWeight_sum_two_pow` and `sum_two_pow_lt_two_pow` — the digit
  dictionary: a subset of bit positions has weight its cardinality, and
  stays inside its block.
* `prod_one_add_mul_pow` — the **two-parameter master identity** over any
  commutative semiring:
  `∏_{j<m} (1 + u·z^{2^j}) = ∑_{n<2^m} u^{w(n)} z^n`.
  The atlas states this for complex `|z| < 1`; here it is exact and
  algebraic, with no convergence hypothesis.
* specializations: the signed finite product
  `∏ (1 - z^{2^j}) = ∑ ε(n) z^n` over any commutative ring (`u = -1`), and
  the binomial weight enumerator `∑ u^{w(n)} = (1+u)^m` (`z = 1`).
* `prod_one_add_eq_sum_powerset` — the sparse form on an arbitrary finite
  set of bit positions, the algebraic engine behind the sparse Prouhet
  identities of the atlas.

The binary dictionary and reindexing kernel come from the canonical
`Finset.equivBitIndices` foundation in `ThueMorseBitSupport`; the product
identities here are then direct finite algebraic expansions.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## The master product identity -/

/-- **Sparse master product.**  Over any commutative semiring, expanding
`∏_{j ∈ S} (1 + x j)` enumerates the subsets of `S`.  This is
`Finset.prod_one_add` in the normalization used by the atlas: the argument
`x` is explicit here, because every call site supplies it. -/
theorem prod_one_add_eq_sum_powerset {R : Type*} [CommSemiring R]
    (S : Finset ℕ) (x : ℕ → R) :
    ∏ j ∈ S, (1 + x j) = ∑ T ∈ S.powerset, ∏ j ∈ T, x j :=
  Finset.prod_one_add (f := x) S

/-- **Two-parameter master identity.**  Over any commutative semiring,
`∏_{j<m} (1 + u·z^{2^j}) = ∑_{n<2^m} u^{w(n)} z^n`: the weighted
enumerator of a dyadic block factorizes completely.  Specializing `u`
and `z` recovers the finite Thue--Morse product, the weight enumerator,
and the Walsh character sums of the atlas. -/
theorem prod_one_add_mul_pow {R : Type*} [CommSemiring R]
    (u z : R) (m : ℕ) :
    ∏ j ∈ range m, (1 + u * z ^ (2 ^ j)) =
      ∑ n ∈ range (2 ^ m), u ^ binaryWeight n * z ^ n := by
  rw [prod_one_add_eq_sum_powerset]
  rw [← sum_powerset_two_pow m (fun n => u ^ binaryWeight n * z ^ n)]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hT' := Finset.mem_powerset.mp hT
  rw [binaryWeight_sum_two_pow hT']
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]

/-- **Finite Thue--Morse product, in full generality.**  Over any
commutative ring, `∏_{j<m} (1 - z^{2^j}) = ∑_{n<2^m} ε(n)·z^n`.  The atlas
and the existing corpus state this over concrete coefficient rings; the
Boolean-cube argument proves it once for all of them. -/
theorem prod_one_sub_pow_eq_sum_thueMorseSign {R : Type*} [CommRing R]
    (z : R) (m : ℕ) :
    ∏ j ∈ range m, (1 - z ^ (2 ^ j)) =
      ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) * z ^ n := by
  have h := prod_one_add_mul_pow (-1 : R) z m
  simp only [neg_one_mul] at h
  calc ∏ j ∈ range m, (1 - z ^ (2 ^ j))
      = ∏ j ∈ range m, (1 + -z ^ (2 ^ j)) := by
        refine Finset.prod_congr rfl fun j _ => by ring
    _ = ∑ n ∈ range (2 ^ m), (-1 : R) ^ binaryWeight n * z ^ n := h
    _ = ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) * z ^ n := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [thueMorseSign]
        push_cast
        ring

/-- **Binomial weight enumerator**, re-derived from the master identity by
setting `z = 1`: the weights of a dyadic block generate `(1 + u)^m`. -/
theorem sum_pow_binaryWeight_eq_one_add_pow {R : Type*} [CommSemiring R]
    (u : R) (m : ℕ) :
    ∑ n ∈ range (2 ^ m), u ^ binaryWeight n = (1 + u) ^ m := by
  have h := prod_one_add_mul_pow u (1 : R) m
  simp only [one_pow, mul_one] at h
  rw [← h, Finset.prod_const, Finset.card_range]

end Fabius

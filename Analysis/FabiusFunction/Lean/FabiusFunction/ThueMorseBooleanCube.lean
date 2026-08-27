import FabiusFunction.DyadicClosedForm

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

The proofs are by induction on the block level, splitting the powerset of
`range (m+1)` by membership of the top bit; no analysis, no `testBit`, and
no divisibility argument is needed anywhere.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## The digit dictionary -/

/-- A sum of distinct powers of two with exponents below `m` stays below
`2 ^ m`.  Mathlib's `Nat.geomSum_lt` in the shape this module uses. -/
theorem sum_two_pow_lt_two_pow {m : ℕ} {T : Finset ℕ}
    (hT : T ⊆ range m) :
    ∑ j ∈ T, 2 ^ j < 2 ^ m :=
  Nat.geomSum_lt le_rfl fun j hj => mem_range.mp (hT hj)

/-- The binary weight of a sum of distinct powers of two is the number of
summands: subsets of bit positions are faithfully encoded. -/
theorem binaryWeight_sum_two_pow {m : ℕ} {T : Finset ℕ}
    (hT : T ⊆ range m) :
    binaryWeight (∑ j ∈ T, 2 ^ j) = T.card := by
  induction m generalizing T with
  | zero =>
      have : T = ∅ := subset_empty.mp (by simpa using hT)
      simp [this, binaryWeight]
  | succ m ih =>
      by_cases hm : m ∈ T
      · have hsub : T.erase m ⊆ range m := by
          intro j hj
          have hj' := hT (mem_of_mem_erase hj)
          have hne := ne_of_mem_erase hj
          simp only [mem_range] at hj' ⊢
          omega
        have hlt := sum_two_pow_lt_two_pow hsub
        have hsplit : ∑ j ∈ T, 2 ^ j =
            2 ^ m + ∑ j ∈ T.erase m, 2 ^ j := by
          rw [← Finset.add_sum_erase _ _ hm]
        rw [hsplit, binaryWeight_add_pow_two m _ hlt, ih hsub,
          ← Finset.card_erase_add_one hm]
      · have hsub : T ⊆ range m := by
          intro j hj
          have hj' := hT hj
          simp only [mem_range] at hj' ⊢
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | rfl
          · exact h
          · exact absurd hj hm
        exact ih hsub

/-! ## The reindexing kernel -/

/-- **Reindexing kernel.**  Summing a function over the subsets of
`range m`, each encoded as a sum of powers of two, is the same as summing
it over the dyadic block `range (2^m)`.  This is the Boolean-cube structure
of the block, stated so that every generating identity of the atlas can be
transported across it. -/
theorem sum_powerset_two_pow {M : Type*} [AddCommMonoid M]
    (m : ℕ) (f : ℕ → M) :
    ∑ T ∈ (range m).powerset, f (∑ j ∈ T, 2 ^ j) =
      ∑ n ∈ range (2 ^ m), f n := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
      -- Split the powerset by membership of the top bit `m`.
      rw [Finset.range_add_one, Finset.powerset_insert, Finset.sum_union, ]
      · -- Split the block into its lower and upper halves.
        have hblock : ∑ n ∈ range (2 ^ (m + 1)), f n =
            ∑ n ∈ range (2 ^ m), f n +
              ∑ n ∈ range (2 ^ m), f (2 ^ m + n) := by
          rw [pow_succ, mul_comm, two_mul, Finset.sum_range_add]
        rw [hblock, ← ih f, ← ih (fun n => f (2 ^ m + n))]
        congr 1
        -- Upper half: subsets containing `m` are `insert m T`.
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl fun T hT => ?_
          have hm : m ∉ T := fun h =>
            absurd (Finset.mem_powerset.mp hT h) (by simp)
          rw [Finset.sum_insert hm]
        · intro T hT U hU hTU
          have hmT : m ∉ T := fun h =>
            absurd (Finset.mem_powerset.mp hT h) (by simp)
          have hmU : m ∉ U := fun h =>
            absurd (Finset.mem_powerset.mp hU h) (by simp)
          have := congrArg (Finset.erase · m) hTU
          simpa [Finset.erase_insert hmT, Finset.erase_insert hmU] using this
      · -- The two families of subsets are disjoint.
        rw [Finset.disjoint_left]
        intro T hT hT'
        have hmT : m ∉ T := fun h =>
          absurd (Finset.mem_powerset.mp hT h) (by simp)
        rcases Finset.mem_image.mp hT' with ⟨U, hU, rfl⟩
        exact hmT (Finset.mem_insert_self m U)

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

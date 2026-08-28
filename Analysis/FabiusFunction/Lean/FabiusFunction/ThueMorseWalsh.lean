import FabiusFunction.ThueMorseBitSupport
import FabiusFunction.ThueMorseBooleanCube
import Mathlib.Data.Nat.Bitwise

/-!
# The Walsh spectrum of the Thue–Morse block

In the Walsh basis the Thue–Morse block is spectrally pure: the sign
vector `(ε(n))_{n<2^m}` *is* the Walsh character indexed by the all-ones
word, so its Walsh transform is a point mass.  This module proves the
atlas's one-point Walsh spectrum together with the plain character
orthogonality it refines, both as specializations of one general Walsh
character sum, on top of a small reusable bit toolkit.

* `sum_range_two_pow` and `testBit_two_pow_sub_one` — the all-ones word:
  `∑_{j<m} 2^j = 2^m - 1`, whose bits are exactly the positions below
  `m`.
* `eq_of_testBit_eq_of_lt_two_pow`, `eq_zero_iff_forall_testBit` and
  `eq_two_pow_sub_one_iff_forall_testBit` — **bounded digit
  extensionality**: below `2^m` a number is determined by its bits below
  `m`, and the two extreme digit patterns pin down `0` and `2^m - 1`.
* `land_sum_two_pow` — masking a sum of distinct two-powers:
  `a &&& ∑_{j∈T} 2^j = ∑_{j∈T, bit_j(a)=1} 2^j`, for every finite `T`.
* `thueMorseSign_eq_neg_one_pow_land` — `ε` as a Walsh character:
  `ε(n) = (-1)^wt((2^m-1) &&& n)` on the block.
* `pow_binaryWeight_eq_prod_ite_testBit` — the **bit factorization of a
  weight power**: `y^wt(n) = ∏_{j<m} (bit_j(n) ? y : 1)` for `n < 2^m`,
  in any commutative monoid.
* `sum_prod_ite_testBit` — the **Walsh kernel**, over an arbitrary
  commutative semiring with an arbitrary weight `x j` per bit position:
  `∑_{n<2^m} ∏_{j<m} (bit_j(n) ? x j : 1) = ∏_{j<m} (1 + x j)`.
* `sum_pow_binaryWeight_mul_pow_binaryWeight_land` — the **general
  masked character sum**, with no hypothesis on `a`:
  `∑_{n<2^m} y^wt(n)·z^wt(a &&& n) = ∏_{j<m} (1 + y·(bit_j(a) ? z : 1))`.
* `sum_neg_one_pow_binaryWeight_land` — **character orthogonality** on
  the dyadic block: for `a < 2^m`, `∑_{n<2^m} (-1)^wt(a &&& n)` is `2^m`
  for `a = 0` and `0` otherwise.  This is the case `y = 1`, `z = -1`.
* `sum_thueMorseSign_mul_walsh` — the **one-point Walsh spectrum**:
  `∑_{n<2^m} ε(n)·(-1)^wt(a &&& n)` is `2^m` for `a = 2^m - 1` and `0`
  for every other `a < 2^m`.  This is the case `y = z = -1`.

The Walsh kernel transports the sum across the Boolean-cube kernel
`sum_powerset_two_pow` and expands `∏ (1 + x j)` over the powerset; the
masked character sum then factors both weight powers over bit positions,
where position `j` contributes `y·(bit_j(a) ? z : 1)`.  The two spectral
statements differ only in which digit pattern of `a` makes every factor
`1 + x j` equal to `2`, so they share a single two-branch argument.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### The all-ones word and bounded digit extensionality -/

/-- The geometric sum of two-powers: `∑_{j<m} 2^j = 2^m - 1`. -/
theorem sum_range_two_pow (m : ℕ) : ∑ j ∈ range m, 2 ^ j = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
      rw [Finset.sum_range_succ, ih, pow_succ]
      omega

/-- The binary digits of `2^m - 1` are exactly the positions below `m`.
This is Lean core's `Nat.testBit_two_pow_sub_one`, kept under the corpus
name because the atlas crosswalk cites it. -/
theorem testBit_two_pow_sub_one (m j : ℕ) :
    (2 ^ m - 1).testBit j = decide (j < m) :=
  Nat.testBit_two_pow_sub_one m j

/-- **Bounded digit extensionality.**  Two naturals below `2^m` that
agree on every bit position below `m` are equal: the high bits of such a
number all vanish, so the low window determines it. -/
theorem eq_of_testBit_eq_of_lt_two_pow {m a b : ℕ} (ha : a < 2 ^ m)
    (hb : b < 2 ^ m) (h : ∀ j < m, a.testBit j = b.testBit j) : a = b := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < m
  · exact h j hj
  · have hpow : (2 : ℕ) ^ m ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha hpow),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb hpow)]

/-- Below `2^m`, only `0` has all of its bits below `m` clear. -/
theorem eq_zero_iff_forall_testBit {m a : ℕ} (ha : a < 2 ^ m) :
    a = 0 ↔ ∀ j < m, a.testBit j = false := by
  constructor
  · rintro rfl j _
    exact Nat.zero_testBit j
  · intro h
    refine eq_of_testBit_eq_of_lt_two_pow ha (Nat.two_pow_pos m) fun j hj => ?_
    rw [h j hj, Nat.zero_testBit]

/-- Below `2^m`, only the all-ones word `2^m - 1` has all of its bits
below `m` set. -/
theorem eq_two_pow_sub_one_iff_forall_testBit {m a : ℕ} (ha : a < 2 ^ m) :
    a = 2 ^ m - 1 ↔ ∀ j < m, a.testBit j = true := by
  have hb : 2 ^ m - 1 < 2 ^ m := by
    have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  constructor
  · rintro rfl j hj
    rw [testBit_two_pow_sub_one]
    exact decide_eq_true hj
  · intro h
    refine eq_of_testBit_eq_of_lt_two_pow ha hb fun j hj => ?_
    rw [h j hj, testBit_two_pow_sub_one]
    exact (decide_eq_true hj).symm

/-! ### Masked two-power sums -/

/-- Masking a sum of distinct two-powers keeps exactly the positions where
the mask has a one: `a &&& ∑_{j∈T} 2^j = ∑_{j∈T, bit_j(a)=1} 2^j`. -/
theorem land_sum_two_pow (a : ℕ) (T : Finset ℕ) :
    a &&& (∑ j ∈ T, 2 ^ j) =
      ∑ j ∈ T.filter (fun j => a.testBit j), 2 ^ j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, testBit_sum_two_pow, testBit_sum_two_pow]
  by_cases hi : i ∈ T <;> cases h : a.testBit i <;>
    simp [hi, h, Finset.mem_filter]

/-- On the dyadic block, the Thue–Morse sign is the Walsh character of the
all-ones word: `ε(n) = (-1)^wt((2^m-1) &&& n)` for `n < 2^m`. -/
theorem thueMorseSign_eq_neg_one_pow_land (m n : ℕ) (hn : n < 2 ^ m) :
    thueMorseSign n = (-1 : ℤ) ^ binaryWeight ((2 ^ m - 1) &&& n) := by
  have hmask : (2 ^ m - 1) &&& n = n := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land, testBit_two_pow_sub_one]
    by_cases him : i < m
    · simp [him]
    · rw [Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) (by omega)))]
      simp [him]
  rw [hmask, thueMorseSign]

/-! ### Characters as products over bit positions -/

private theorem prod_ite_const {R : Type*} [CommMonoid R] (s : Finset ℕ)
    (p : ℕ → Prop) [DecidablePred p] (y : R) :
    ∏ j ∈ s, (if p j then y else 1) = y ^ (s.filter p).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]

/-- **Bit factorization of a weight power.**  For `n < 2^m` and any `y`
in a commutative monoid, `y^wt(n) = ∏_{j<m} (bit_j(n) ? y : 1)`: the
weight power splits into one factor per bit position of the block. -/
theorem pow_binaryWeight_eq_prod_ite_testBit {R : Type*} [CommMonoid R]
    (y : R) {m n : ℕ} (hn : n < 2 ^ m) :
    y ^ binaryWeight n =
      ∏ j ∈ range m, (if n.testBit j then y else 1) := by
  have hhigh : ∀ j, ¬ j < m → n.testBit j = false := by
    intro j hj
    exact Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) (by omega)))
  have hmem : ∀ j, j ∈ (range m).filter (fun j => n.testBit j = true) ↔
      n.testBit j = true := by
    intro j
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    by_contra hj
    rw [hhigh j hj] at h
    simp at h
  have hsub : (range m).filter (fun j => n.testBit j = true) ⊆ range m :=
    Finset.filter_subset _ _
  have hsum :
      ∑ j ∈ (range m).filter (fun j => n.testBit j = true), 2 ^ j = n := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [testBit_sum_two_pow]
    by_cases hi : n.testBit i = true
    · rw [hi]
      exact decide_eq_true ((hmem i).mpr hi)
    · have hif : n.testBit i = false := by simpa using hi
      rw [hif]
      exact decide_eq_false fun hc => hi ((hmem i).mp hc)
  have hcard := binaryWeight_sum_two_pow hsub
  rw [hsum] at hcard
  rw [hcard, prod_ite_const (range m) (fun j => n.testBit j = true) y]

/-! ### The Walsh kernel -/

/-- **The Walsh kernel.**  Over an arbitrary commutative semiring, with an
arbitrary weight `x j` attached to each bit position,
`∑_{n<2^m} ∏_{j<m} (bit_j(n) ? x j : 1) = ∏_{j<m} (1 + x j)`.  Summing a
multiplicative bit weight over the dyadic block is the same as expanding
the product of `1 + x j`: the block is the Boolean cube, and the two
sides are the two ways of enumerating its vertices. -/
theorem sum_prod_ite_testBit {R : Type*} [CommSemiring R] (m : ℕ)
    (x : ℕ → R) :
    ∑ n ∈ range (2 ^ m), ∏ j ∈ range m, (if n.testBit j then x j else 1) =
      ∏ j ∈ range m, (1 + x j) := by
  rw [← sum_powerset_two_pow m
      (fun n => ∏ j ∈ range m, (if n.testBit j then x j else 1)),
    prod_one_add_eq_sum_powerset]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTsub := Finset.mem_powerset.mp hT
  have hbit : ∀ j ∈ range m,
      (if (∑ i ∈ T, 2 ^ i).testBit j then x j else 1) =
        (if j ∈ T then x j else 1) := by
    intro j _
    rw [testBit_sum_two_pow]
    by_cases hj : j ∈ T
    · rw [if_pos (decide_eq_true hj), if_pos hj]
    · have hd : ¬ (decide (j ∈ T) = true) := by simp [hj]
      rw [if_neg hd, if_neg hj]
  rw [Finset.prod_congr rfl hbit, Finset.prod_ite_mem,
    Finset.inter_eq_right.mpr hTsub]

/-- **The general masked character sum.**  Over an arbitrary commutative
semiring and for every mask `a`,
`∑_{n<2^m} y^wt(n)·z^wt(a &&& n) = ∏_{j<m} (1 + y·(bit_j(a) ? z : 1))`.
Both weight powers factor over bit positions, and position `j` of the
summand contributes `y` always and `z` only where the mask has a one.  No
bound on `a` is needed: masking never leaves the block. -/
theorem sum_pow_binaryWeight_mul_pow_binaryWeight_land {R : Type*}
    [CommSemiring R] (y z : R) (m a : ℕ) :
    ∑ n ∈ range (2 ^ m), y ^ binaryWeight n * z ^ binaryWeight (a &&& n) =
      ∏ j ∈ range m, (1 + y * (if a.testBit j then z else 1)) := by
  rw [← sum_prod_ite_testBit m (fun j => y * (if a.testBit j then z else 1))]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : n < 2 ^ m := Finset.mem_range.mp hn
  have hland : a &&& n < 2 ^ m := lt_of_le_of_lt Nat.and_le_right hn'
  rw [pow_binaryWeight_eq_prod_ite_testBit y hn',
    pow_binaryWeight_eq_prod_ite_testBit z hland,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Nat.testBit_land]
  cases n.testBit j <;> cases a.testBit j <;> simp

/-! ### Orthogonality and the one-point spectrum -/

private theorem prod_one_add_eq_two_pow (m : ℕ) (x : ℕ → ℤ)
    (h : ∀ j < m, x j = 1) : ∏ j ∈ range m, (1 + x j) = 2 ^ m := by
  have hbit : ∀ j ∈ range m, (1 : ℤ) + x j = 2 := by
    intro j hj
    rw [h j (Finset.mem_range.mp hj)]
    norm_num
  rw [Finset.prod_congr rfl hbit, Finset.prod_const, Finset.card_range]

private theorem prod_one_add_eq_zero (m : ℕ) (x : ℕ → ℤ) {j : ℕ}
    (hj : j < m) (hx : x j = -1) : ∏ i ∈ range m, (1 + x i) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_range.mpr hj) ?_
  rw [hx]
  norm_num

/-- **Character orthogonality on the dyadic block.**  For `a < 2^m`,
`∑_{n<2^m} (-1)^wt(a &&& n)` is `2^m` when `a = 0` and `0` otherwise:
a nontrivial Walsh character sums to zero over the Boolean group. -/
theorem sum_neg_one_pow_binaryWeight_land (m a : ℕ) (ha : a < 2 ^ m) :
    ∑ n ∈ range (2 ^ m), (-1 : ℤ) ^ binaryWeight (a &&& n) =
      if a = 0 then (2 ^ m : ℤ) else 0 := by
  have hone : ∀ n ∈ range (2 ^ m),
      (-1 : ℤ) ^ binaryWeight (a &&& n) =
        (1 : ℤ) ^ binaryWeight n * (-1 : ℤ) ^ binaryWeight (a &&& n) := by
    intro n _
    rw [one_pow, one_mul]
  rw [Finset.sum_congr rfl hone,
    sum_pow_binaryWeight_mul_pow_binaryWeight_land (1 : ℤ) (-1 : ℤ) m a]
  by_cases h0 : a = 0
  · rw [if_pos h0]
    refine prod_one_add_eq_two_pow m
      (fun j => (1 : ℤ) * (if a.testBit j then (-1 : ℤ) else 1))
      fun j hj => ?_
    norm_num [(eq_zero_iff_forall_testBit ha).mp h0 j hj]
  · rw [if_neg h0]
    obtain ⟨j, hjm, hjbit⟩ : ∃ j, j < m ∧ a.testBit j = true := by
      by_contra hcon
      refine h0 ((eq_zero_iff_forall_testBit ha).mpr fun i hi => ?_)
      by_cases hb : a.testBit i = true
      · exact absurd ⟨i, hi, hb⟩ hcon
      · simpa using hb
    exact prod_one_add_eq_zero m
      (fun j => (1 : ℤ) * (if a.testBit j then (-1 : ℤ) else 1)) hjm
      (by norm_num [hjbit])

/-- **The Walsh transform of the Thue–Morse block is a point mass.**  For
`a < 2^m`, `∑_{n<2^m} ε(n)·(-1)^wt(a &&& n)` is `2^m` at the all-ones
word `a = 2^m - 1` and `0` at every other `a`: the block is spectrally
pure in the Walsh basis. -/
theorem sum_thueMorseSign_mul_walsh (m a : ℕ) (ha : a < 2 ^ m) :
    ∑ n ∈ range (2 ^ m), thueMorseSign n * (-1 : ℤ) ^ binaryWeight (a &&& n) =
      if a = 2 ^ m - 1 then (2 ^ m : ℤ) else 0 := by
  have hsign : ∀ n ∈ range (2 ^ m),
      thueMorseSign n * (-1 : ℤ) ^ binaryWeight (a &&& n) =
        (-1 : ℤ) ^ binaryWeight n * (-1 : ℤ) ^ binaryWeight (a &&& n) := by
    intro n _
    rw [thueMorseSign]
  rw [Finset.sum_congr rfl hsign,
    sum_pow_binaryWeight_mul_pow_binaryWeight_land (-1 : ℤ) (-1 : ℤ) m a]
  by_cases hall : a = 2 ^ m - 1
  · rw [if_pos hall]
    refine prod_one_add_eq_two_pow m
      (fun j => (-1 : ℤ) * (if a.testBit j then (-1 : ℤ) else 1))
      fun j hj => ?_
    norm_num [(eq_two_pow_sub_one_iff_forall_testBit ha).mp hall j hj]
  · rw [if_neg hall]
    obtain ⟨j, hjm, hjbit⟩ : ∃ j, j < m ∧ a.testBit j = false := by
      by_contra hcon
      refine hall ((eq_two_pow_sub_one_iff_forall_testBit ha).mpr
        fun i hi => ?_)
      by_cases hb : a.testBit i = true
      · exact hb
      · exact absurd ⟨i, hi, by simpa using hb⟩ hcon
    exact prod_one_add_eq_zero m
      (fun j => (-1 : ℤ) * (if a.testBit j then (-1 : ℤ) else 1)) hjm
      (by norm_num [hjbit])

end Fabius

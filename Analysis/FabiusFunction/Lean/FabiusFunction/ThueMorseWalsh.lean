import FabiusFunction.ThueMorseLucasSupport

/-!
# The Walsh spectrum of the Thue–Morse block

In the Walsh basis the Thue–Morse block is spectrally pure: the sign
vector `(ε(n))_{n<2^m}` *is* the Walsh character indexed by the all-ones
word, so its Walsh transform is a point mass.  This module proves the
atlas's one-point Walsh spectrum together with the plain character
orthogonality it refines, on top of a small reusable bit toolkit.

* `sum_range_two_pow` and `testBit_two_pow_sub_one` — the all-ones word:
  `∑_{j<m} 2^j = 2^m - 1`, whose bits are exactly the positions below
  `m`.
* `land_sum_two_pow` — masking a sum of distinct two-powers:
  `a &&& ∑_{j∈T} 2^j = ∑_{j∈T, bit_j(a)=1} 2^j`, for every finite `T`.
* `thueMorseSign_eq_neg_one_pow_land` — `ε` as a Walsh character:
  `ε(n) = (-1)^wt((2^m-1) &&& n)` on the block.
* `sum_neg_one_pow_binaryWeight_land` — **character orthogonality** on
  the dyadic block: `∑_{n<2^m} (-1)^wt(a &&& n)` is `2^m` for `a = 0`
  and `0` otherwise.
* `sum_thueMorseSign_mul_walsh` — the **one-point Walsh spectrum**:
  `∑_{n<2^m} ε(n)·(-1)^wt(a &&& n)` is `2^m` for `a = 2^m - 1` and `0`
  for every other `a < 2^m`.

The proofs transport the sums across the Boolean-cube kernel
`sum_powerset_two_pow` and factor each character as a product over bit
positions, where every position contributes `1 ± 1`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### The all-ones word and masked two-power sums -/

/-- The geometric sum of two-powers: `∑_{j<m} 2^j = 2^m - 1`. -/
theorem sum_range_two_pow (m : ℕ) : ∑ j ∈ range m, 2 ^ j = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
      rw [Finset.sum_range_succ, ih, pow_succ]
      omega

/-- The binary digits of `2^m - 1` are exactly the positions below `m`. -/
theorem testBit_two_pow_sub_one (m j : ℕ) :
    (2 ^ m - 1).testBit j = decide (j < m) := by
  rw [← sum_range_two_pow, testBit_sum_two_pow, decide_eq_decide]
  exact Finset.mem_range

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

/-! ### Character products over bit positions -/

private theorem prod_ite_neg_one (T : Finset ℕ) (p : ℕ → Prop)
    [DecidablePred p] :
    ∏ j ∈ T, (if p j then (-1 : ℤ) else 1) =
      (-1) ^ (T.filter p).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]

/-! ### Orthogonality and the one-point spectrum -/

/-- **Character orthogonality on the dyadic block.**  For `a < 2^m`,
`∑_{n<2^m} (-1)^wt(a &&& n)` is `2^m` when `a = 0` and `0` otherwise:
a nontrivial Walsh character sums to zero over the Boolean group. -/
theorem sum_neg_one_pow_binaryWeight_land (m a : ℕ) (ha : a < 2 ^ m) :
    ∑ n ∈ range (2 ^ m), (-1 : ℤ) ^ binaryWeight (a &&& n) =
      if a = 0 then (2 ^ m : ℤ) else 0 := by
  rw [← sum_powerset_two_pow m (fun n => (-1 : ℤ) ^ binaryWeight (a &&& n))]
  have hterm : ∀ T ∈ (range m).powerset,
      (-1 : ℤ) ^ binaryWeight (a &&& ∑ j ∈ T, 2 ^ j) =
      ∏ j ∈ T, (if a.testBit j then (-1 : ℤ) else 1) := by
    intro T hT
    have hTsub := Finset.mem_powerset.mp hT
    rw [land_sum_two_pow,
      binaryWeight_sum_two_pow ((Finset.filter_subset _ _).trans hTsub),
      ← prod_ite_neg_one]
  rw [Finset.sum_congr rfl hterm, ← prod_one_add_eq_sum_powerset]
  by_cases h0 : a = 0
  · subst h0
    rw [if_pos rfl]
    have hbit : ∀ j ∈ range m,
        (1 : ℤ) + (if (0 : ℕ).testBit j then (-1 : ℤ) else 1) = 2 := by
      intro j _
      rw [Nat.zero_testBit]
      norm_num
    rw [Finset.prod_congr rfl hbit, Finset.prod_const, Finset.card_range]
  · rw [if_neg h0]
    have hj : ∃ j, j < m ∧ a.testBit j = true := by
      by_contra hcon
      apply h0
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.zero_testBit]
      by_cases him : i < m
      · by_contra hbit
        exact hcon ⟨i, him, by simpa using hbit⟩
      · exact Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega)))
    obtain ⟨j, hjm, hjbit⟩ := hj
    refine Finset.prod_eq_zero (Finset.mem_range.mpr hjm) ?_
    rw [hjbit]
    norm_num

/-- **The Walsh transform of the Thue–Morse block is a point mass.**  For
`a < 2^m`, `∑_{n<2^m} ε(n)·(-1)^wt(a &&& n)` is `2^m` at the all-ones
word `a = 2^m - 1` and `0` at every other `a`: the block is spectrally
pure in the Walsh basis. -/
theorem sum_thueMorseSign_mul_walsh (m a : ℕ) (ha : a < 2 ^ m) :
    ∑ n ∈ range (2 ^ m), thueMorseSign n * (-1 : ℤ) ^ binaryWeight (a &&& n) =
      if a = 2 ^ m - 1 then (2 ^ m : ℤ) else 0 := by
  rw [← sum_powerset_two_pow m
    (fun n => thueMorseSign n * (-1 : ℤ) ^ binaryWeight (a &&& n))]
  have hterm : ∀ T ∈ (range m).powerset,
      thueMorseSign (∑ j ∈ T, 2 ^ j) *
        (-1 : ℤ) ^ binaryWeight (a &&& ∑ j ∈ T, 2 ^ j) =
      ∏ j ∈ T, (if a.testBit j then (1 : ℤ) else -1) := by
    intro T hT
    have hTsub := Finset.mem_powerset.mp hT
    rw [thueMorseSign, binaryWeight_sum_two_pow hTsub, land_sum_two_pow,
      binaryWeight_sum_two_pow ((Finset.filter_subset _ _).trans hTsub),
      ← prod_ite_neg_one, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases h : a.testBit j <;> simp [h]
  rw [Finset.sum_congr rfl hterm, ← prod_one_add_eq_sum_powerset]
  by_cases hall : a = 2 ^ m - 1
  · subst hall
    rw [if_pos rfl]
    have hbit : ∀ j ∈ range m,
        (1 : ℤ) + (if (2 ^ m - 1).testBit j then (1 : ℤ) else -1) = 2 := by
      intro j hj
      rw [testBit_two_pow_sub_one,
        if_pos (by simpa using Finset.mem_range.mp hj)]
      norm_num
    rw [Finset.prod_congr rfl hbit, Finset.prod_const, Finset.card_range]
  · rw [if_neg hall]
    have hj : ∃ j, j < m ∧ a.testBit j = false := by
      by_contra hcon
      apply hall
      apply Nat.eq_of_testBit_eq
      intro i
      rw [testBit_two_pow_sub_one]
      by_cases him : i < m
      · have : a.testBit i = true := by
          by_contra hbit
          exact hcon ⟨i, him, by simpa using hbit⟩
        rw [this]
        simp [him]
      · rw [Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega)))]
        simp [him]
    obtain ⟨j, hjm, hjbit⟩ := hj
    refine Finset.prod_eq_zero (Finset.mem_range.mpr hjm) ?_
    rw [hjbit]
    norm_num

end Fabius

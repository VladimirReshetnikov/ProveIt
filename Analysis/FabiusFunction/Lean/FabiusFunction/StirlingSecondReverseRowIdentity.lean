import FabiusFunction.StirlingSecondReverseRow

/-!
# Finite reindexings of the second-kind reverse-row recurrence

The core theorem `second_reverse_row_ring_Icc` already proves
`eq:second-reverse-row` of `thm:second-reverse-recurrences` in the canonical
`Combinatorial_Coefficient_Calculus` monograph over every ring and for every
row. This companion gives two finite reindexings of that same theorem:

* `second_reverse_row_range` shifts the manuscript index by `j = i+2`,
  so the sum runs over `range (n-k)` for every positive column `k`.
* `second_reverse_row_sum_ring` uses the actual Stirling column index `m`;
  its kernel is zero below `q+2`, where the entry recovered has column `q+1`.
* `second_reverse_row_sum` preserves the rational specialization of the
  column-indexed sum.

No second generating-function argument is needed. The shifted range follows
from the exact interval by translation. Splitting off the zero kernel terms
and using binomial symmetry gives the column-indexed sum. All coefficients
are integer casts, so even the factor reordering is valid in a ring that is
not commutative. Boundary rows, including empty sums at and above the
diagonal, require no additional hypothesis.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **The reverse-row recurrence with a zero-based summation index.**

This is `eq:second-reverse-row` with `j = i+2`, over every ring.
Only positivity of the column is required: when `n ≤ k` the sum is empty
and the left side vanishes. No division or characteristic assumption is used. -/
theorem second_reverse_row_range {R : Type*} [Ring R]
    (n k : ℕ) (hk : 1 ≤ k) :
    ((n : R) - (k : R)) * (Nat.stirlingSecond n k : R) =
      ∑ i ∈ range (n - k),
        (-1 : R) ^ (i + 2) * (i.factorial : R) *
          ((k + i + 1).choose (i + 2) : R) *
          (Nat.stirlingSecond n (k + i + 1) : R) := by
  rw [second_reverse_row_ring_Icc R n k hk,
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    show n - k + 1 + 1 - 2 = n - k by omega]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show 2 + i = i + 2 by omega, Nat.add_sub_cancel,
    show k + (i + 2) - 1 = k + i + 1 by omega]

/-- **The reverse-row recurrence as a finite column-indexed Stirling transform.**

For every `n` and `q`, the kernel is supported on `m ≥ q+2`, strictly to the
right of column `q+1`. The result holds in every ring: the Stirling-number
cast commutes with the integer-valued kernel even without commutativity of
the ambient ring. Subtraction on the left is ring subtraction. -/
theorem second_reverse_row_sum_ring {R : Type*} [Ring R] (n q : ℕ) :
    ((n : R) - ((q + 1 : ℕ) : R)) * (Nat.stirlingSecond n (q + 1) : R) =
      ∑ m ∈ range (n + 1), (Nat.stirlingSecond n m : R) *
        (if q + 2 ≤ m then
          (-1 : R) ^ (m - q) * ((m - q - 2).factorial : R) * (m.choose q : R)
        else 0) := by
  by_cases hqn : q + 1 ≤ n
  · rw [second_reverse_row_range n (q + 1) (by omega)]
    let T : ℕ → R := fun m => (Nat.stirlingSecond n m : R) *
      (if q + 2 ≤ m then
        (-1 : R) ^ (m - q) * ((m - q - 2).factorial : R) * (m.choose q : R)
      else 0)
    have hzero : (∑ m ∈ range (q + 2), T m) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      dsimp only [T]
      rw [if_neg (by have := Finset.mem_range.mp hm; omega), mul_zero]
    change (∑ i ∈ range (n - (q + 1)),
      (-1 : R) ^ (i + 2) * (i.factorial : R) *
        ((q + 1 + i + 1).choose (i + 2) : R) *
        (Nat.stirlingSecond n (q + 1 + i + 1) : R)) =
      ∑ m ∈ range (n + 1), T m
    rw [← Finset.sum_range_add_sum_Ico T (show q + 2 ≤ n + 1 by omega),
      hzero, zero_add, Finset.sum_Ico_eq_sum_range,
      show n + 1 - (q + 2) = n - (q + 1) by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [T]
    rw [if_pos (by omega), show q + 2 + i - q = i + 2 by omega,
      Nat.add_sub_cancel, show q + 2 + i = q + (i + 2) by omega,
      Nat.choose_symm_add, show q + (i + 2) = q + 1 + i + 1 by omega]
    exact (Nat.cast_comm (Nat.stirlingSecond n (q + 1 + i + 1))
      ((-1 : R) ^ (i + 2) * (i.factorial : R) *
        ((q + 1 + i + 1).choose (i + 2) : R))).symm
  · have hnq : n < q + 1 := by omega
    rw [Nat.stirlingSecond_eq_zero_of_lt hnq, Nat.cast_zero, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg (by have := Finset.mem_range.mp hm; omega), mul_zero]

/-- The rational specialization of the column-indexed reverse-row identity.
This retains the unrestricted `n,q` signature of the original
`second_reverse_row_sum`; its stronger ring version is
`second_reverse_row_sum_ring`. -/
theorem second_reverse_row_sum (n q : ℕ) :
    ((n : ℚ) - ((q + 1 : ℕ) : ℚ)) * (Nat.stirlingSecond n (q + 1) : ℚ) =
      ∑ m ∈ range (n + 1), (Nat.stirlingSecond n m : ℚ) *
        (if q + 2 ≤ m then
          (-1 : ℚ) ^ (m - q) * ((m - q - 2).factorial : ℚ) * (m.choose q : ℚ)
        else 0) :=
  second_reverse_row_sum_ring n q

end Fabius

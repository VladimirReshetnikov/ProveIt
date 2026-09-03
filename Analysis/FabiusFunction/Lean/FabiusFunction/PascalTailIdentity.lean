import Mathlib.Data.Nat.Choose.Sum

/-!
# The Pascal tail identity

For every `j` and `k`,

`∑_{h ≤ j} C(h, k) · 2^(j-h) + ∑_{i ≤ k} C(j+1, i) = 2^(j+1)`.

Read with `k = r - 1`, the second sum is `Q_r(j) = ∑_{i < r} C(j+1, i)`, the
number of subsets of a `(j+1)`-element set with fewer than `r` elements, and
the identity is the Spectra volume's "Pascal tail identity"
`∑_{h ≤ j} C(h, r-1) 2^(j-h) = 2^(j+1) - Q_r(j)`, which counts the subsets
with at least `r` elements by the position of their `r`-th largest element.
It is the finite form behind the digital zero count of the Pascal–Rvachev
hierarchy: the left sum is the number of zeros of `Φ_r` below `2^(j+1)`
counted with multiplicity, layer by layer.

The identity is stated additively so that it holds in `ℕ` without any
side condition, and the subtraction form is derived from it.  The proof is an
induction on `j` in which both sums grow by one term: the left one gains
`C(j+1, k)` and doubles, the right one satisfies
`Q(j+1) + C(j+1, k) = 2·Q(j)` by Pascal's rule.
-/

set_option autoImplicit false

open Finset

namespace PascalTail

/-- The tail count `Q(j, k) = ∑_{i ≤ k} C(j+1, i)`: subsets of a
`(j+1)`-element set with at most `k` elements. -/
def tailCount (j k : ℕ) : ℕ := ∑ i ∈ range (k + 1), (j + 1).choose i

/-- **Pascal's rule for the tail count**: `Q(j+1, k) + C(j+1, k) = 2·Q(j, k)`. -/
theorem tailCount_succ_add (j k : ℕ) :
    tailCount (j + 1) k + (j + 1).choose k = 2 * tailCount j k := by
  unfold tailCount
  -- peel the first term of `Q(j+1, k)` and apply Pascal's rule to the rest
  have hpeel : ∑ i ∈ range (k + 1), (j + 2).choose i =
      1 + (∑ i ∈ range k, (j + 1).choose i + ∑ i ∈ range k, (j + 1).choose (i + 1)) := by
    -- after peeling, Pascal's rule `C(j+2, i+1) = C(j+1, i) + C(j+1, i+1)` is
    -- definitional, so `congr` closes the summand goal by `rfl`
    rw [Finset.sum_range_succ', Nat.choose_zero_right, ← Finset.sum_add_distrib, add_comm]
    congr 1
  -- the two peelings of `Q(j, k)`
  have hlast : ∑ i ∈ range (k + 1), (j + 1).choose i =
      ∑ i ∈ range k, (j + 1).choose i + (j + 1).choose k :=
    Finset.sum_range_succ _ _
  have hfirst : ∑ i ∈ range (k + 1), (j + 1).choose i =
      ∑ i ∈ range k, (j + 1).choose (i + 1) + 1 := by
    rw [Finset.sum_range_succ', Nat.choose_zero_right]
  rw [hpeel]
  omega

/-- **The Pascal tail identity**, additive form:
`∑_{h ≤ j} C(h, k) · 2^(j-h) + Q(j, k) = 2^(j+1)`. -/
theorem sum_choose_mul_two_pow_add_tailCount (j k : ℕ) :
    ∑ h ∈ range (j + 1), h.choose k * 2 ^ (j - h) + tailCount j k = 2 ^ (j + 1) := by
  induction j with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, Nat.sub_self, pow_zero, mul_one, tailCount]
    -- `C(0, k) + ∑_{i ≤ k} C(1, i) = 2`, by cases on `k`
    cases k with
    | zero => simp
    | succ k =>
      rw [Nat.choose_zero_succ, zero_add, Finset.sum_range_succ', Nat.choose_zero_right]
      -- `∑_{i < k+1} C(1, i+1) = 1`: only `i = 0` contributes
      have : ∑ i ∈ range (k + 1), (1 : ℕ).choose (i + 1) = 1 := by
        rw [Finset.sum_range_succ']
        simp [Nat.choose_eq_zero_of_lt]
      rw [this]
      norm_num
  | succ j ih =>
    -- the left sum gains its top term and doubles
    have hsplit : ∑ h ∈ range (j + 2), h.choose k * 2 ^ (j + 1 - h) =
        2 * ∑ h ∈ range (j + 1), h.choose k * 2 ^ (j - h) + (j + 1).choose k := by
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun h hh => ?_
      have hle : h ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
      rw [Nat.succ_sub hle, pow_succ]
      ring
    have hQ := tailCount_succ_add j k
    rw [hsplit, pow_succ]
    omega

/-- The Pascal tail identity in the volume's subtraction form:
`∑_{h ≤ j} C(h, k) · 2^(j-h) = 2^(j+1) - Q(j, k)`. -/
theorem sum_choose_mul_two_pow_eq (j k : ℕ) :
    ∑ h ∈ range (j + 1), h.choose k * 2 ^ (j - h) = 2 ^ (j + 1) - tailCount j k := by
  have := sum_choose_mul_two_pow_add_tailCount j k
  omega

/-- The tail count never exceeds `2^(j+1)`: it counts subsets of a
`(j+1)`-element set. -/
theorem tailCount_le (j k : ℕ) : tailCount j k ≤ 2 ^ (j + 1) := by
  have := sum_choose_mul_two_pow_add_tailCount j k
  omega

end PascalTail

import FabiusFunction.BellPolynomialInversion
import FabiusFunction.BellStirling
import FabiusFunction.LahNumbers

/-!
# Partial exponential Bell polynomials

The partial exponential Bell polynomial `B_{n,k}(x_1, x_2, …)` is the total
weight of the partitions of an `n`-element labelled set into `k` blocks, a
block of size `i` weighing `x_i`.  Choosing the block that contains the
largest element (it has `i+1` elements, `i` of them chosen among the other
`n`) gives the recurrence

`B_{n+1,k+1} = ∑_{i ≤ n} C(n,i) x_{i+1} B_{n-i,k}`,  `B_{0,0} = 1`,

which we take as the definition, over any commutative semiring, for a weight
sequence `x : ℕ → R` (the value `x 0` is never used).  The recurrence is the
binomial convolution of the shifted weights with the previous column
(`Bell.binomialConv`), so the whole calculus of exponential generating
functions developed in `BellPolynomialInversion` applies.

* `Bell.complete x n = ∑_k B_{n,k}`: the complete Bell polynomials of the
  moment–cumulant modules are the row sums of the partial ones.
* The specializations `B_{n,k}(1,1,…) = S(n,k)`, `B_{n,k}(0!,1!,2!,…) = c(n,k)`
  and `B_{n,k}(1!,2!,3!,…) = L(n,k)`: Stirling numbers of both kinds and Lah
  numbers count set partitions, permutations and lists respectively, and each
  satisfies the block-of-the-largest-element recurrence.

## Main results

* `partialBell`, `partialBell_succ_succ`, `partialBell_eq_zero_of_lt`,
  `partialBell_self`.
* `bell_complete_eq_sum_partialBell`.
* `partialBell_one`, `stirlingFirst_succ_succ_eq_sum`,
  `partialBell_factorial_pred`, `lahNumber_succ_succ_eq_sum`,
  `partialBell_factorial`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The partial exponential Bell polynomials `B_{n,k}(x_1, x_2, …)`, defined by
the recurrence `B_{n+1,k+1} = ∑_{i ≤ n} C(n,i) x_{i+1} B_{n-i,k}` with
`B_{0,0} = 1` and zero boundary.  The weight `x i` is attached to blocks of
size `i`; `x 0` is unused. -/
noncomputable def partialBell (x : ℕ → R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      ∑ i ∈ Finset.range (n + 1), (n.choose i : R) * (x (i + 1) * partialBell x (n - i) k)
termination_by n _ => n
decreasing_by omega

/-- `B_{0,0} = 1`. -/
@[simp] theorem partialBell_zero_zero (x : ℕ → R) : partialBell x 0 0 = 1 := by
  rw [partialBell]

/-- `B_{0,k+1} = 0`: no partition of the empty set into `k+1` parts. -/
@[simp] theorem partialBell_zero_succ (x : ℕ → R) (k : ℕ) : partialBell x 0 (k + 1) = 0 := by
  rw [partialBell]

/-- `B_{n+1,0} = 0`: no partition of a nonempty set into no parts. -/
@[simp] theorem partialBell_succ_zero (x : ℕ → R) (n : ℕ) : partialBell x (n + 1) 0 = 0 := by
  rw [partialBell]

/-- The block-of-the-largest-element recurrence. -/
theorem partialBell_succ_succ (x : ℕ → R) (n k : ℕ) :
    partialBell x (n + 1) (k + 1) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : R) * (x (i + 1) * partialBell x (n - i) k) := by
  rw [partialBell]

/-- The recurrence as a binomial convolution of the shifted weights with the
previous column. -/
theorem partialBell_succ_succ_eq_binomialConv (x : ℕ → R) (n k : ℕ) :
    partialBell x (n + 1) (k + 1) =
      Bell.binomialConv (Bell.shift x) (fun j => partialBell x j k) n := by
  rw [partialBell_succ_succ, Bell.binomialConv_eq_sum_range]
  rfl

/-- `B_{n,k} = 0` for `n < k`: a set cannot have more blocks than elements. -/
theorem partialBell_eq_zero_of_lt (x : ℕ → R) : ∀ {n k : ℕ}, n < k → partialBell x n k = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => by simp
  | n + 1, k + 1, h => by
    rw [partialBell_succ_succ]
    apply Finset.sum_eq_zero
    intro i _
    rw [partialBell_eq_zero_of_lt x (show n - i < k by omega), mul_zero, mul_zero]

/-- `B_{n,n} = x_1^n`: only singleton blocks. -/
theorem partialBell_self (x : ℕ → R) (n : ℕ) : partialBell x n n = x 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [partialBell_succ_succ, Finset.sum_range_succ', Finset.sum_eq_zero, zero_add]
    · simp [ih, pow_succ, mul_comm]
    · intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      rw [partialBell_eq_zero_of_lt x (show n - (i + 1) < n by omega), mul_zero, mul_zero]

/-- **Row sums are the complete Bell polynomials:**
`Bell.complete x n = ∑_{k ≤ n} B_{n,k}(x)`. -/
theorem bell_complete_eq_sum_partialBell (x : ℕ → R) (n : ℕ) :
    Bell.complete x n = ∑ k ∈ Finset.range (n + 1), partialBell x n k := by
  have h := Bell.eq_complete_of_recurrence x (fun n => ∑ k ∈ Finset.range (n + 1), partialBell x n k)
    (by simp) (by
      intro n
      rw [Bell.binomialConv_comm, Bell.binomialConv_eq_sum_range]
      -- peel the vanishing k = 0 column and expand the recurrence
      rw [Finset.sum_range_succ', partialBell_succ_zero, add_zero]
      simp only [partialBell_succ_succ]
      rw [Finset.sum_comm]
      -- the inner sums extend to `range (n+1)` because `B_{n-i,k} = 0` for `k > n - i`
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [← Finset.mul_sum, ← Finset.mul_sum, Bell.shift_apply]
      congr 2
      symm
      apply Finset.sum_subset (Finset.range_mono (show n - i + 1 ≤ n + 1 by omega))
      intro k _ hk
      have hk' : n - i < k := by
        rw [Finset.mem_range, not_lt] at hk
        omega
      exact partialBell_eq_zero_of_lt x hk')
  exact (congrFun h n).symm

end CommSemiring

/-! ### Specializations -/

section Specializations

/-- `B_{n,k}(1,1,1,…) = S(n,k)`: unweighted partitions are counted by the Stirling
numbers of the second kind. -/
theorem partialBell_one (n k : ℕ) : partialBell (fun _ => (1 : ℕ)) n k = Nat.stirlingSecond n k := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    cases n with
    | zero =>
      cases k with
      | zero => simp
      | succ k => simp
    | succ n =>
      cases k with
      | zero => simp
      | succ k =>
        rw [partialBell_succ_succ, stirlingSecond_succ_succ_eq_sum,
          ← Finset.sum_range_reflect (fun i => n.choose i * Nat.stirlingSecond i k) (n + 1)]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hsub : n + 1 - 1 - i = n - i := by omega
        rw [hsub, Nat.choose_symm hin, ih (n - i) (by omega) k, one_mul, Nat.cast_id]

end Specializations

end Fabius

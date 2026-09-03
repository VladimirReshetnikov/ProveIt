import FabiusFunction.BellHomogeneity

/-!
# `r`-Stirling numbers of the second kind

The `r`-Stirling numbers `S_r(n,k)` count partitions of `[n]` into `k` blocks in which the labels
`1, …, r` lie in distinct blocks.  Here they are defined by their recurrence
`S_r(n,k) = k S_r(n-1,k) + S_r(n-1,k-1)` (`n > r`), `S_r(r,r) = 1`, in the shifted indices
`T_r(n,k) = S_r(n+r,k+r)` (`rStirlingShift`, `rStirling`).  The binomial-convolution structure of
the recurrence gives the explicit formula

`S_r(n+r,k+r) = ∑_j C(n,j) r^{n-j} S(j,k)`

(`rStirlingShift_eq_binomialConv`, `rStirlingShift_eq_sum`), and with it the mixed exponential
generating function

`∑_n (∑_k S_r(n+r,k+r) y^k) z^n/n! = e^{rz} exp(y(e^z - 1))`

(`egfA_rStirlingPoly`).

## Main results

* `rStirlingShift`, `rStirling`, `rStirling_self`, `rStirling_succ_zero`, `rStirling_succ_succ`.
* `binomialConv_const_mul_left`, `binomialConv_const_mul_right`, `binomialConv_zero_right`.
* `rStirlingShift_eq_binomialConv`, `rStirlingShift_eq_sum`, `rStirling_eq_sum`.
* `rStirlingPoly_eq_binomialConv`, `egfA_rStirlingPoly`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The `r`-Stirling numbers in shifted indices, `T_r(n,k) = S_r(n+r,k+r)`, by the recurrence
`T(n+1,k) = (k+r) T(n,k) + T(n,k-1)`. -/
def rStirlingShift (r : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => r * rStirlingShift r n 0
  | n + 1, k + 1 => (k + 1 + r) * rStirlingShift r n (k + 1) + rStirlingShift r n k

/-- The `r`-Stirling numbers `S_r(n,k)`, zero unless `r ≤ k` and `r ≤ n`. -/
def rStirling (r n k : ℕ) : ℕ :=
  if r ≤ n ∧ r ≤ k then rStirlingShift r (n - r) (k - r) else 0

/-- The shifted `r`-Stirling triangle starts at `1`. -/
@[simp] theorem rStirlingShift_zero_zero (r : ℕ) : rStirlingShift r 0 0 = 1 := rfl

/-- Row `0` of the shifted `r`-Stirling triangle vanishes beyond
its first entry. -/
@[simp] theorem rStirlingShift_zero_succ (r k : ℕ) : rStirlingShift r 0 (k + 1) = 0 := rfl

/-- Column `0` of the shifted `r`-Stirling triangle multiplies by `r` at each step. -/
theorem rStirlingShift_succ_zero (r n : ℕ) :
    rStirlingShift r (n + 1) 0 = r * rStirlingShift r n 0 := rfl

/-- The shifted `r`-Stirling recurrence. -/
theorem rStirlingShift_succ_succ (r n k : ℕ) :
    rStirlingShift r (n + 1) (k + 1) =
      (k + 1 + r) * rStirlingShift r n (k + 1) + rStirlingShift r n k := rfl

/-- `S_r(r,r) = 1`. -/
theorem rStirling_self (r : ℕ) : rStirling r r r = 1 := by
  simp [rStirling]

/-- `S_r(n+1,0) = 0`. -/
theorem rStirling_succ_zero (r n : ℕ) : rStirling r (n + 1) 0 = 0 := by
  unfold rStirling
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [rStirlingShift_succ_zero]
  · rw [if_neg (fun h => by omega)]

/-- **The `r`-Stirling recurrence:** `S_r(n+1,k+1) = (k+1) S_r(n,k+1) + S_r(n,k)` for `n ≥ r`. -/
theorem rStirling_succ_succ (r n k : ℕ) (hn : r ≤ n) :
    rStirling r (n + 1) (k + 1) = (k + 1) * rStirling r n (k + 1) + rStirling r n k := by
  unfold rStirling
  rcases le_or_gt r (k + 1) with hk | hk
  · rw [if_pos ⟨by omega, hk⟩, if_pos ⟨hn, hk⟩]
    rcases lt_or_ge k r with hk' | hk'
    · have hkr : k + 1 = r := by omega
      rw [if_neg (fun h => by omega), show n + 1 - r = (n - r) + 1 by omega,
        show k + 1 - r = 0 by omega, rStirlingShift_succ_zero, add_zero, hkr]
    · rw [if_pos ⟨hn, hk'⟩, show n + 1 - r = (n - r) + 1 by omega,
        show k + 1 - r = (k - r) + 1 by omega, rStirlingShift_succ_succ,
        show k - r + 1 + r = k + 1 by omega]
  · simp [show ¬ (r ≤ n + 1 ∧ r ≤ k + 1) by omega, show ¬ (r ≤ n ∧ r ≤ k + 1) by omega,
      show ¬ (r ≤ n ∧ r ≤ k) by omega]

/-! ### Linearity of the binomial convolution -/

section Conv

variable {R : Type*} [CommSemiring R]

/-- The binomial convolution is homogeneous in its left argument. -/
theorem binomialConv_const_mul_left (c : R) (a b : ℕ → R) (n : ℕ) :
    Bell.binomialConv (fun j => c * a j) b n = c * Bell.binomialConv a b n := by
  rw [Bell.binomialConv_eq_sum_range, Bell.binomialConv_eq_sum_range, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The binomial convolution is homogeneous in its right argument. -/
theorem binomialConv_const_mul_right (c : R) (a b : ℕ → R) (n : ℕ) :
    Bell.binomialConv a (fun j => c * b j) n = c * Bell.binomialConv a b n := by
  rw [Bell.binomialConv_eq_sum_range, Bell.binomialConv_eq_sum_range, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The binomial convolution against the zero sequence vanishes. -/
theorem binomialConv_zero_right (a : ℕ → R) (n : ℕ) :
    Bell.binomialConv a (fun _ => 0) n = 0 := by
  rw [Bell.binomialConv_eq_sum_range]
  simp

end Conv

/-! ### The explicit formula -/

/-- `T_r(n,k)` is the binomial convolution of `j ↦ r^j` with `j ↦ S(j,k)`. -/
theorem rStirlingShift_eq_binomialConv (r n k : ℕ) :
    rStirlingShift r n k =
      Bell.binomialConv (fun j => r ^ j) (fun j => Nat.stirlingSecond j k) n := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [Bell.binomialConv_eq_sum_range]
    | succ k => simp [Bell.binomialConv_eq_sum_range, Nat.stirlingSecond_zero_succ]
  | succ n ih =>
    have hu : Bell.shift (fun j => r ^ j) = fun j => r * r ^ j :=
      funext fun j => by simp [Bell.shift_apply, pow_succ']
    cases k with
    | zero =>
      have hv : Bell.shift (fun j => Nat.stirlingSecond j 0) = fun _ => 0 :=
        funext fun j => by simp [Bell.shift_apply, Nat.stirlingSecond_succ_zero]
      rw [rStirlingShift_succ_zero, ih, Bell.binomialConv_succ, hv, hu, binomialConv_zero_right,
        binomialConv_const_mul_left, zero_add]
    | succ k =>
      have hv : Bell.shift (fun j => Nat.stirlingSecond j (k + 1)) =
          (fun j => (k + 1) * Nat.stirlingSecond j (k + 1)) + fun j => Nat.stirlingSecond j k :=
        funext fun j => by simp only [Bell.shift_apply, Pi.add_apply, Nat.stirlingSecond_succ_succ]
      rw [rStirlingShift_succ_succ, ih, ih, Bell.binomialConv_succ, hv, Bell.binomialConv_add_right,
        Pi.add_apply, hu, binomialConv_const_mul_left, binomialConv_const_mul_right]
      ring

/-- **The explicit formula:** `S_r(n+r,k+r) = ∑_j C(n,j) S(j,k) r^{n-j}`. -/
theorem rStirlingShift_eq_sum (r n k : ℕ) :
    rStirlingShift r n k =
      ∑ j ∈ range (n + 1), n.choose j * (Nat.stirlingSecond j k * r ^ (n - j)) := by
  rw [rStirlingShift_eq_binomialConv, Bell.binomialConv_comm, Bell.binomialConv_eq_sum_range]
  simp only [Nat.cast_id]

/-- The explicit formula in the original indices: for `r ≤ n` and `r ≤ k`,
`S_r(n,k) = ∑_j C(n-r,j) S(j,k-r) r^{n-r-j}`. -/
theorem rStirling_eq_sum (r n k : ℕ) (hn : r ≤ n) (hk : r ≤ k) :
    rStirling r n k =
      ∑ j ∈ range (n - r + 1), (n - r).choose j * (Nat.stirlingSecond j (k - r) * r ^ (n - r - j)) := by
  rw [rStirling, if_pos ⟨hn, hk⟩, rStirlingShift_eq_sum]

/-! ### The mixed generating function -/

/-- The row polynomial `∑_k S_r(n+r,k+r) y^k` is the binomial convolution of `j ↦ r^j` with the
Touchard polynomials `B_m(y,…,y) = ∑_k S(m,k) y^k`. -/
theorem rStirlingPoly_eq_binomialConv (r n : ℕ) :
    (∑ k ∈ range (n + 1), (rStirlingShift r n k : Polynomial ℚ) * Polynomial.X ^ k) =
      Bell.binomialConv (fun j => (r : Polynomial ℚ) ^ j)
        (fun m => Bell.complete (fun _ => (Polynomial.X : Polynomial ℚ)) m) n := by
  rw [Bell.binomialConv_eq_sum_range]
  simp only [rStirlingShift_eq_binomialConv, Bell.binomialConv_eq_sum_range, Nat.cast_id,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Finset.sum_mul, bell_complete_const, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  symm
  refine (Finset.sum_subset
    (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega))
    fun k hk hk' => ?_).trans (Finset.sum_congr rfl fun k _ => ?_)
  · rw [Finset.mem_range, not_lt] at hk'
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, mul_zero, mul_zero]
  · ring

/-- **The mixed exponential generating function:**
`∑_n (∑_k S_r(n+r,k+r) y^k) z^n/n! = e^{rz} exp(y(e^z - 1))`. -/
theorem egfA_rStirlingPoly (r : ℕ) :
    egfA (Polynomial ℚ) (fun n =>
        ∑ k ∈ range (n + 1), (rStirlingShift r n k : Polynomial ℚ) * Polynomial.X ^ k) =
      PowerSeries.rescale (r : Polynomial ℚ) (PowerSeries.exp (Polynomial ℚ)) *
        (PowerSeries.exp (Polynomial ℚ)).subst
          (PowerSeries.C (Polynomial.X : Polynomial ℚ) * (PowerSeries.exp (Polynomial ℚ) - 1)) := by
  rw [← PowerSeries.smul_eq_C_mul, ← bellWeightSeries_const, exp_subst_bellWeightSeries]
  have hr : PowerSeries.rescale (r : Polynomial ℚ) (PowerSeries.exp (Polynomial ℚ)) =
      egfA (Polynomial ℚ) (fun j => (r : Polynomial ℚ) ^ j) := by
    ext n
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, coeff_egfA, mul_comm]
  rw [hr, egfA_mul]
  congr 1
  funext n
  exact rStirlingPoly_eq_binomialConv r n

end Fabius

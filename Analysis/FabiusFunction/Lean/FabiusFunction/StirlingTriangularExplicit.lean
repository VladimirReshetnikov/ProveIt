import FabiusFunction.StirlingBasisChange

/-!
# The triangular explicit formula for Stirling numbers of the second kind

Dividing the surjection count `k^n = ∑_{r ≤ k} S(n,r) k!/(k-r)!` by `k!` and
isolating the term `r = k` gives

`S(n,k) = k^n/k! - ∑_{r < k} S(n,r)/(k-r)!`,

a recursion in `k` along a row that uses only earlier entries of the same row.

## Main results

* `pow_div_factorial_eq_sum_stirlingSecond_div_factorial`,
  `stirlingSecond_eq_pow_div_factorial_sub_sum`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- `k^n / k! = ∑_{r ≤ k} S(n,r) / (k-r)!` in `ℚ`. -/
theorem pow_div_factorial_eq_sum_stirlingSecond_div_factorial (n k : ℕ) :
    ((k : ℚ) ^ n) / k.factorial =
      ∑ r ∈ Finset.range (k + 1), (Nat.stirlingSecond n r : ℚ) / (k - r).factorial := by
  have h := pow_eq_sum_stirlingSecond_mul_factorial_mul_choose k n
  -- both index sets can be replaced by `range (n + k + 1)`
  have h1 : ∑ r ∈ Finset.range (n + 1), Nat.stirlingSecond n r * (r.factorial * k.choose r)
      = ∑ r ∈ Finset.range (n + k + 1), Nat.stirlingSecond n r * (r.factorial * k.choose r) := by
    refine Finset.sum_subset ?_ ?_
    · exact Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega)
    · intro r _ hr
      rw [Finset.mem_range, not_lt] at hr
      rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), zero_mul]
  have h2 : ∑ r ∈ Finset.range (k + 1), Nat.stirlingSecond n r * (r.factorial * k.choose r)
      = ∑ r ∈ Finset.range (n + k + 1), Nat.stirlingSecond n r * (r.factorial * k.choose r) := by
    refine Finset.sum_subset ?_ ?_
    · exact Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega)
    · intro r _ hr
      rw [Finset.mem_range, not_lt] at hr
      rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero, mul_zero]
  have h' : ((k : ℚ) ^ n) = ∑ r ∈ Finset.range (k + 1),
      (Nat.stirlingSecond n r : ℚ) * (r.factorial * k.choose r) := by
    rw [h1, ← h2] at h
    exact_mod_cast h
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  rw [div_eq_iff hk, Finset.sum_mul, h']
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrk : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hfac : (k.choose r : ℚ) * r.factorial * (k - r).factorial = k.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hrk
  have hne : ((k - r).factorial : ℚ) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hne]
  calc (Nat.stirlingSecond n r : ℚ) * (r.factorial * k.choose r) * (k - r).factorial
      = (Nat.stirlingSecond n r : ℚ) * ((k.choose r : ℚ) * r.factorial * (k - r).factorial) := by
        ring
    _ = _ := by rw [hfac]

/-- **The triangular explicit formula:** `S(n,k) = k^n/k! - ∑_{r < k} S(n,r)/(k-r)!`. -/
theorem stirlingSecond_eq_pow_div_factorial_sub_sum (n k : ℕ) :
    (Nat.stirlingSecond n k : ℚ) =
      ((k : ℚ) ^ n) / k.factorial -
        ∑ r ∈ Finset.range k, (Nat.stirlingSecond n r : ℚ) / (k - r).factorial := by
  rw [pow_div_factorial_eq_sum_stirlingSecond_div_factorial, Finset.sum_range_succ, Nat.sub_self,
    Nat.factorial_zero, Nat.cast_one, div_one, add_sub_cancel_left]

end Fabius

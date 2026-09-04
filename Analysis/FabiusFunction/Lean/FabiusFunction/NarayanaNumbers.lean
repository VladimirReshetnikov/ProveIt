import FabiusFunction.CatalanGeneratingFunction
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Narayana numbers

The Narayana numbers are defined here by the division-free determinant expression

`N(n,k) = C(n,k) C(n-1,k-1) - C(n,k-1) C(n-1,k)`,

taken in `ℤ` (`narayana`), which is automatically `0` outside `1 ≤ k ≤ n` and so needs no side
condition.  The manuscript's closed form `N(n,k) = C(n,k) C(n,k-1) / n` appears here in the
division-free shape `n N(n,k) = C(n,k) C(n,k-1)` (`narayana_mul`), the symmetry is
`narayana_symm`, and the row sum is the Catalan number (`sum_narayana`).

The combinatorial reading of `N(n,k)` as the number of Dyck paths of semilength `n` with `k`
peaks is not formalized.

## Main results

* `narayana`, `narayana_succ_succ`, `narayana_zero_right`, `narayana_mul`.
* `narayana_symm`.
* `sum_choose_mul_choose_succ`, `succ_mul_catalan_succ`, `sum_narayana`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The Narayana number `N(n,k)`, as the `2×2` determinant
`C(n,k) C(n-1,k-1) - C(n,k-1) C(n-1,k)`.  This vanishes unless `1 ≤ k ≤ n`. -/
def narayana (n k : ℕ) : ℤ :=
  (n.choose k : ℤ) * ((n - 1).choose (k - 1) : ℤ) -
    (n.choose (k - 1) : ℤ) * ((n - 1).choose k : ℤ)

/-- The shifted form, free of truncated subtraction. -/
theorem narayana_succ_succ (m j : ℕ) :
    narayana (m + 1) (j + 1) =
      ((m + 1).choose (j + 1) : ℤ) * (m.choose j : ℤ) -
        ((m + 1).choose j : ℤ) * (m.choose (j + 1) : ℤ) := rfl

/-- `N(n,0) = 0`. -/
@[simp] theorem narayana_zero_right (n : ℕ) : narayana n 0 = 0 := by
  simp [narayana]

/-- **The closed form, division-free:** `n N(n,k) = C(n,k) C(n,k-1)`. -/
theorem narayana_mul (m j : ℕ) :
    ((m : ℤ) + 1) * narayana (m + 1) (j + 1) =
      ((m + 1).choose (j + 1) : ℤ) * ((m + 1).choose j : ℤ) := by
  rcases le_or_gt (j + 1) (m + 1) with hj | hj
  · have hjm : j ≤ m := Nat.lt_succ_iff.mp hj
    -- `k C(n,k) = (n-k+1) C(n,k-1)` and `n C(n-1,k) = (n-k) C(n,k)`
    have h1 : ((m + 1).choose (j + 1) : ℤ) * ((j : ℤ) + 1) =
        ((m + 1).choose j : ℤ) * ((m : ℤ) + 1 - j) := by
      have hc := Nat.choose_succ_right_eq (m + 1) j
      have hcast := congrArg (fun t : ℕ => (t : ℤ)) hc
      push_cast [Nat.cast_sub (show j ≤ m + 1 by omega)] at hcast
      linarith [hcast]
    have h2 : ((m : ℤ) + 1) * (m.choose j : ℤ) =
        ((m + 1).choose j : ℤ) * ((m : ℤ) + 1 - j) := by
      have := Nat.succ_mul_choose_eq m j
      have hcast := congrArg (fun t : ℕ => (t : ℤ)) this
      push_cast at hcast
      have h3 := Nat.choose_succ_right_eq (m + 1) j
      have hcast3 := congrArg (fun t : ℕ => (t : ℤ)) h3
      push_cast [Nat.cast_sub (show j ≤ m + 1 by omega)] at hcast3
      linarith [hcast, hcast3]
    have h4 : ((m : ℤ) + 1) * (m.choose (j + 1) : ℤ) =
        ((m + 1).choose (j + 1) : ℤ) * ((m : ℤ) - j) := by
      have := Nat.succ_mul_choose_eq m (j + 1)
      have hcast := congrArg (fun t : ℕ => (t : ℤ)) this
      push_cast at hcast
      have h5 := Nat.choose_succ_right_eq (m + 1) (j + 1)
      have hcast5 := congrArg (fun t : ℕ => (t : ℤ)) h5
      rcases le_or_gt (j + 1) m with hjm' | hjm'
      · push_cast [Nat.cast_sub (show j + 1 ≤ m + 1 by omega),
          Nat.cast_sub (show j ≤ m by omega)] at hcast5
        linarith [hcast, hcast5]
      · have hjeq : j = m := by omega
        subst hjeq
        simp [Nat.choose_succ_self]
    rw [narayana_succ_succ]
    nlinarith [h1, h2, h4]
  · have hjm : m < j := by omega
    have e1 : (m + 1).choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have e2 : m.choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [narayana_succ_succ, e1, e2]
    push_cast
    ring

/-- **Symmetry:** `N(n,k) = N(n, n+1-k)`. -/
theorem narayana_symm (m j : ℕ) (hj : j ≤ m) :
    narayana (m + 1) (j + 1) = narayana (m + 1) (m - j + 1) := by
  have hne : ((m : ℤ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  rw [narayana_mul m j, narayana_mul m (m - j)]
  have c1 : (m + 1).choose (m - j + 1) = (m + 1).choose j := by
    rw [show m - j + 1 = (m + 1) - j by omega, Nat.choose_symm (by omega)]
  have c3 : (m + 1).choose (m - j) = (m + 1).choose (j + 1) := by
    rw [show m - j = (m + 1) - (j + 1) by omega, Nat.choose_symm (by omega)]
  rw [c1, c3]
  ring

/-- `∑_{j<m+1} C(m+1,j) C(m+1,j+1) = C(2m+2, m)`. -/
theorem sum_choose_mul_choose_succ (m : ℕ) :
    ∑ j ∈ range (m + 1), ((m + 1).choose j * (m + 1).choose (j + 1)) =
      (2 * m + 2).choose m := by
  have hV := Nat.add_choose_eq (m + 1) (m + 1) m
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hV
  rw [show 2 * m + 2 = (m + 1) + (m + 1) by ring, hV]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  congr 1
  rw [show m - j = (m + 1) - (j + 1) by omega, Nat.choose_symm (by omega)]

/-- `(m+1) · catalan (m+1) = C(2m+2, m)`. -/
theorem succ_mul_catalan_succ (m : ℕ) :
    (m + 1) * catalan (m + 1) = (2 * m + 2).choose m := by
  have h1 := catalan_succ_eq_choose_sub_choose m
  have h2 := succ_mul_catalan_eq_centralBinom (m + 1)
  rw [Nat.centralBinom_eq_two_mul_choose] at h2
  have hle : (2 * (m + 1)).choose m ≤ (2 * (m + 1)).choose (m + 1) :=
    Nat.choose_le_succ_of_lt_half_left (by omega)
  rw [show 2 * (m + 1) = 2 * m + 2 from by ring] at h1 h2 hle
  -- the subtraction in `h1` is exact, so `catalan (m+1) + C(2m+2,m) = C(2m+2,m+1)`
  have hcat : catalan (m + 1) + (2 * m + 2).choose m = (2 * m + 2).choose (m + 1) := by
    rw [h1]
    exact Nat.sub_add_cancel hle
  have hstep : (m + 1 + 1) * catalan (m + 1) = catalan (m + 1) + (2 * m + 2).choose m := by
    rw [h2, hcat]
  -- cancel one copy of `catalan (m+1)`; `omega` cannot, the products are nonlinear
  have key : (m + 1) * catalan (m + 1) + catalan (m + 1)
      = (2 * m + 2).choose m + catalan (m + 1) := by
    calc (m + 1) * catalan (m + 1) + catalan (m + 1)
        = (m + 1 + 1) * catalan (m + 1) := by ring
      _ = catalan (m + 1) + (2 * m + 2).choose m := hstep
      _ = (2 * m + 2).choose m + catalan (m + 1) := by ring
  exact Nat.add_right_cancel key

/-- **The row sum:** `∑_{k=1}^{n} N(n,k) = C_n`. -/
theorem sum_narayana (m : ℕ) :
    ∑ j ∈ range (m + 1), narayana (m + 1) (j + 1) = catalan (m + 1) := by
  have hmul : ((m : ℤ) + 1) * ∑ j ∈ range (m + 1), narayana (m + 1) (j + 1) =
      ((2 * m + 2).choose m : ℤ) := by
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun j _ => narayana_mul m j]
    have := sum_choose_mul_choose_succ m
    have hcast := congrArg (fun t : ℕ => (t : ℤ)) this
    push_cast at hcast
    rw [← hcast]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hc := succ_mul_catalan_succ m
  have hccast := congrArg (fun t : ℕ => (t : ℤ)) hc
  push_cast at hccast
  have hne : ((m : ℤ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  rw [hmul, ← hccast]

end Fabius

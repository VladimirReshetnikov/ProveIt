/-
Added for ProveIt (not an upstream file; distributed under Apache-2.0).
A local inductive proof of the power expansion in descending factorials,
needed by the quantitative port on Mathlib v4.32.0. No upstream proof text
is copied.
-/
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

private theorem mul_descFactorial_step (a k : ℕ) :
    a * a.descFactorial k = a.descFactorial (k + 1) + k * a.descFactorial k := by
  by_cases hk : k ≤ a
  · rw [Nat.descFactorial_succ, ← add_mul, Nat.sub_add_cancel hk]
  · have h := Nat.descFactorial_of_lt (Nat.lt_of_not_ge hk)
    rw [Nat.descFactorial_succ, h]
    simp

theorem Nat.pow_eq_sum_stirlingSecond_mul_descFactorial (a n : ℕ) :
    a ^ n = ∑ k ∈ Finset.range (n + 1), n.stirlingSecond k * a.descFactorial k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hshift :
        (∑ k ∈ Finset.range (n + 1), (k + 1) * n.stirlingSecond (k + 1) *
          a.descFactorial (k + 1)) =
        ∑ k ∈ Finset.range (n + 1), k * n.stirlingSecond k * a.descFactorial k := by
      have h := Finset.sum_range_succ' (fun k => k * n.stirlingSecond k * a.descFactorial k)
        (n + 1)
      rw [Finset.sum_range_succ] at h
      simpa only [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n),
        mul_zero, zero_mul, add_zero] using h.symm
    rw [pow_succ', ih, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.stirlingSecond_succ_zero, zero_mul, add_zero,
      Nat.stirlingSecond_succ_succ]
    calc
      _ = (∑ k ∈ Finset.range (n + 1), k * n.stirlingSecond k * a.descFactorial k) +
          ∑ k ∈ Finset.range (n + 1), n.stirlingSecond k * a.descFactorial (k + 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        calc
          a * (n.stirlingSecond k * a.descFactorial k) =
              n.stirlingSecond k * (a * a.descFactorial k) := by ring
          _ = n.stirlingSecond k * (a.descFactorial (k + 1) + k * a.descFactorial k) := by
            rw [mul_descFactorial_step]
          _ = _ := by ring
      _ = _ := by
        rw [← hshift, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring

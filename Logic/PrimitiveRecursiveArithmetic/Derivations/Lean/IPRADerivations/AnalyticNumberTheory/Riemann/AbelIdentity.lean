import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Imported from the packet `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`,
`AbelIdentity.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Finite Abel summation for rational series prefixes and a monotone
inverse weight. These statements do not require a limit of the series. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.AbelIdentity
open scoped BigOperators

/-- Increments are indexed by their right endpoint. -/
theorem summation_by_parts (u S M : ℕ → ℚ)
    (initial : M 0 = u 0 * S 0)
    (delta : ∀ i, M (i+1) - M i = u (i+1)*(S (i+1)-S i)) (n : ℕ) :
    M n = u n*S n - ∑ i ∈ Finset.range n, (u (i+1)-u i)*S i := by
  induction n with
  | zero => simpa using initial
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := delta n
    nlinarith only [h, ih]

/-- Total variation of the weight times the uniform bound on prefixes. -/
theorem correction_bound (u S : ℕ → ℚ) (B : ℚ) (hu : Monotone u)
    (n : ℕ) (hS : ∀ i ≤ n, |S i| ≤ B) :
    |∑ i ∈ Finset.range n, (u (i+1)-u i)*S i| ≤ (u n-u 0)*B := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hd := sub_nonneg.mpr (hu (Nat.le_succ n))
    have term : |(u (n+1)-u n)*S n| ≤ (u (n+1)-u n)*B := by
      rw [abs_mul, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_left (hS n (Nat.le_succ n)) hd
    rw [Finset.sum_range_succ]
    calc
      _ ≤ |∑ i ∈ Finset.range n, (u (i+1)-u i)*S i| + |(u (n+1)-u n)*S n| := abs_add_le ..
      _ ≤ (u n-u 0)*B + (u (n+1)-u n)*B :=
        add_le_add (ih fun i hi => hS i (Nat.le_trans hi (Nat.le_succ n))) term
      _ = _ := by ring

/-- A bounded prefix of the weighted series yields the original growth estimate. -/
theorem recover (u S M : ℕ → ℚ) (B : ℚ) (hu : Monotone u) (hu0 : 0 ≤ u 0)
    (hS0 : S 0 = 0) (hM0 : M 0 = 0)
    (delta : ∀ i, M (i+1)-M i = u (i+1)*(S (i+1)-S i))
    (n : ℕ) (hS : ∀ i ≤ n, |S i| ≤ B) : |M n| ≤ 2*B*u n := by
  have hun : 0 ≤ u n := hu0.trans (hu (Nat.zero_le n))
  have hB : 0 ≤ B := (abs_nonneg _).trans (hS 0 (Nat.zero_le _))
  have initial : M 0 = u 0 * S 0 := by simp [hS0, hM0]
  rw [summation_by_parts u S M initial delta n]
  calc
    _ ≤ |u n*S n| + |∑ i ∈ Finset.range n, (u (i+1)-u i)*S i| := abs_sub ..
    _ ≤ u n*B + (u n-u 0)*B := by
      rw [abs_mul, abs_of_nonneg hun]
      exact add_le_add (mul_le_mul_of_nonneg_left (hS n (Nat.le_refl _)) hun)
        (correction_bound u S B hu n hS)
    _ ≤ 2*B*u n := by nlinarith [mul_nonneg hu0 hB]

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.AbelIdentity

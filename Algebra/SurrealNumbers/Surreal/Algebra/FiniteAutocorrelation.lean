import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Finite autocorrelation bounds over ordered rings

Elementary finite energy inequalities for `trigonometry:cor:coeffbounds`.
Zero extension and the inequality `2ab ≤ a² + b²` suffice; no analytic norm,
infinite summation or Archimedean hypothesis is used.
-/

namespace Surreal.FiniteAutocorrelation

open Finset

variable {F : Type*} [CommRing F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Shifting a nonnegative finitely supported sequence can only decrease its total sum. -/
theorem sum_shift_le (a : ℕ → F) (N k : ℕ) (ha : ∀ j, 0 ≤ a j)
    (hz : ∀ j, N < j → a j = 0) :
    ∑ j ∈ range (N + 1), a (j + k) ≤ ∑ j ∈ range (N + 1), a j := by
  have he := sum_range_add a k (N + 1)
  have hf := sum_range_add a (N + 1) k
  have hz' : ∑ j ∈ range k, a (N + 1 + j) = 0 :=
    sum_eq_zero fun j _ => hz _ (by omega)
  rw [hz', add_zero, Nat.add_comm (N + 1) k] at hf
  rw [hf] at he
  have hp : 0 ≤ ∑ j ∈ range k, a j := sum_nonneg fun j _ => ha j
  simpa only [Nat.add_comm k] using (show
    ∑ j ∈ range (N + 1), a (k + j) ≤ ∑ j ∈ range (N + 1), a j by linarith)

/-- Each autocorrelation is bounded by the total squared energy. -/
theorem autocorrelation_le_sum_sq (a : ℕ → F) (N k : ℕ)
    (hz : ∀ j, N < j → a j = 0) :
    ∑ j ∈ range (N + 1), a (j + k) * a j ≤ ∑ j ∈ range (N + 1), a j ^ 2 := by
  have hshift := sum_shift_le (fun j => a j ^ 2) N k (fun j => sq_nonneg (a j))
    (fun j hj => by rw [hz j hj, zero_pow (by decide : 2 ≠ 0)])
  have hpoint : ∑ j ∈ range (N + 1), 2 * (a (j + k) * a j) ≤
      ∑ j ∈ range (N + 1), (a (j + k) ^ 2 + a j ^ 2) := by
    apply sum_le_sum
    intro j _
    nlinarith [sq_nonneg (a (j + k) - a j)]
  rw [← mul_sum, sum_add_distrib] at hpoint
  linarith

/-- Twice the endpoint product is bounded by the total squared energy when endpoints differ. -/
theorem two_mul_endpoints_le_sum_sq (a : ℕ → F) (N : ℕ) (hN : 0 < N) :
    2 * (a N * a 0) ≤ ∑ j ∈ range (N + 1), a j ^ 2 := by
  have hs : ({0, N} : Finset ℕ) ⊆ range (N + 1) := by
    intro j hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp
  have he := sum_le_sum_of_subset_of_nonneg hs (fun j _ _ => sq_nonneg (a j))
  simp only [sum_pair (Ne.symm hN.ne')] at he
  nlinarith [sq_nonneg (a N - a 0)]

end Surreal.FiniteAutocorrelation

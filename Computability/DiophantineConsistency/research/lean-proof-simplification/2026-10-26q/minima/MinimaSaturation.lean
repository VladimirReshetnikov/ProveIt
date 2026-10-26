import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

namespace MinimaSaturation
open scoped BigOperators

/-- Equality in a sum of lower bounds is equivalent to equality in every block. -/
theorem sum_at_lower_bounds {ι : Type*} [Fintype ι]
    (value lower : ι → ℤ) (h : ∀ i, lower i ≤ value i) :
    (∑ i, value i) = (∑ i, lower i) ↔ ∀ i, value i = lower i := by
  simpa only [Finset.mem_univ, forall_true_left, eq_comm] using
    (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => h i))

/-- A semantic form accommodates coupled blocks and nonzero minima. -/
theorem sum_at_lower_bounds_iff {ι : Type*} [Fintype ι]
    (value lower : ι → ℤ) (P : ι → Prop)
    (h : ∀ i, lower i ≤ value i)
    (hP : ∀ i, value i = lower i ↔ P i) :
    (∑ i, value i) = (∑ i, lower i) ↔ ∀ i, P i := by
  rw [sum_at_lower_bounds value lower h]
  exact forall_congr' hP

-- Exact expression copied from MinimumNorm.minima76 at reviewed commit.
def minima76 (n0 n1 na W nk rt : ℤ) : ℤ :=
  n0 ^ 2 + n1 ^ 2 + na ^ 2 + W ^ 2 + (nk - 1) ^ 2 + rt ^ 2 - 3

/-- Exact statement of the existing theorem; new body uses five block minima. -/
theorem minima76_zero_iff (n0 n1 na W nk rt : ℤ)
    (h0 : 1 ≤ n0 ^ 2) (h0eq : n0 ^ 2 = 1 ↔ n0 = 1)
    (h1 : 1 ≤ n1 ^ 2) (h1eq : n1 ^ 2 = 1 ↔ n1 = 1)
    (ha : 1 ≤ na ^ 2 + W ^ 2) (haeq : na ^ 2 + W ^ 2 = 1 ↔ na = 1 ∧ W = 0) :
    minima76 n0 n1 na W nk rt = 0 ↔
      n0 = 1 ∧ n1 = 1 ∧ na = 1 ∧ W = 0 ∧ nk = 1 ∧ rt = 0 := by
  have h := sum_at_lower_bounds
    (![n0 ^ 2, n1 ^ 2, na ^ 2 + W ^ 2, (nk - 1) ^ 2, rt ^ 2] : Fin 5 → ℤ)
    ![1, 1, 1, 0, 0] (by
      intro i
      fin_cases i <;> dsimp <;>
        first | exact h0 | exact h1 | exact ha | exact sq_nonneg _)
  rw [minima76, sub_eq_zero]
  simpa [Fin.sum_univ_succ, Fin.forall_fin_succ,
    add_assoc, h0eq, h1eq, haeq, sq_eq_zero_iff, sub_eq_zero, and_assoc] using h

#print axioms sum_at_lower_bounds
#print axioms sum_at_lower_bounds_iff
#print axioms minima76_zero_iff
end MinimaSaturation

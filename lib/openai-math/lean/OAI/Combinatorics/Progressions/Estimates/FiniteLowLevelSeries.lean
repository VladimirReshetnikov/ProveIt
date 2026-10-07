import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem low_level_series_bound {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) (r : ℕ) :
    (∑ j ∈ Finset.range r, u ^ (j + 1)) ≤ 2 * u := by
  have hs (n : ℕ) : (∑ j ∈ Finset.range n, u ^ j) ≤ 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [geom_sum_succ]
        nlinarith [mul_le_mul_of_nonneg_left ih hu0]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul]
  nlinarith [mul_le_mul_of_nonneg_right (hs r) hu0]

end Erdos3

end

end OAI

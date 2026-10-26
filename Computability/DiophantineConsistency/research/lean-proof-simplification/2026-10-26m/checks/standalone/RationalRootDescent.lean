import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace ProveItReview

/-- Preserve the actual signed rational root when descending an integral power. -/
theorem rat_intCast_num_of_pow {q : ℚ} {z : ℤ} {n : ℕ}
    (hn : n ≠ 0) (h : q ^ n = (z : ℚ)) : (q.num : ℚ) = q := by
  apply Rat.coe_int_num_of_den_eq_one
  simpa [hn] using congrArg Rat.den h

example {q : ℚ} {z : ℤ} (h : q ^ 2 = (z : ℚ)) :
    ∃ k : ℤ, (k : ℚ) = q ∧ k ^ 2 = z := by
  have hq := rat_intCast_num_of_pow (by decide : 2 ≠ 0) h
  refine ⟨q.num, hq, ?_⟩
  exact_mod_cast (show (q.num : ℚ) ^ 2 = (z : ℚ) by rwa [hq])

#print axioms rat_intCast_num_of_pow
end ProveItReview

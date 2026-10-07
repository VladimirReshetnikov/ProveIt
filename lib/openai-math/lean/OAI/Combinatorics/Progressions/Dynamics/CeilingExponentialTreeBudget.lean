import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3

theorem ceil_exp_branch_count {n : ℕ} {B : ℝ}
    (hn : (n : ℝ) ≤ Real.exp B) : n ≤ ⌈Real.exp B⌉₊ :=
  Nat.cast_le.mp (hn.trans (Nat.le_ceil _))

theorem ceiling_exp_tree_vertices_le (depth : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (((depth + 1) * (max 1 ⌈Real.exp B⌉₊) ^ depth : ℕ) : ℝ) ≤
      Real.exp (((depth : ℝ) + 1) + (depth : ℝ) * (B + 1)) := by
  have hceil : 1 ≤ ⌈Real.exp B⌉₊ := Nat.one_le_ceil_iff.mpr (Real.exp_pos B)
  have hdepth : (depth : ℝ) + 1 ≤ Real.exp ((depth : ℝ) + 1) := by
    linarith [Real.add_one_le_exp ((depth : ℝ) + 1)]
  rw [max_eq_right hceil, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  calc
    _ ≤ Real.exp ((depth : ℝ) + 1) * (Real.exp (B + 1)) ^ depth :=
      mul_le_mul hdepth
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (ceil_exp_le_exp_add_one hB) depth)
        (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

end Erdos3

end

end OAI

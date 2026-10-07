import OAI.Combinatorics.Progressions.Estimates.PhysicalActiveIdealSite

namespace OAI

section

namespace Erdos3

noncomputable def idealSiteBoxRadius (α : Type*) [Fintype α] (degree : ℕ) : ℝ :=
  (2 : ℝ) ^ Fintype.card α * (partitionedIdealRadius α degree + 1)

theorem idealSiteBoxRadius_pos (α : Type*) [Fintype α] (degree : ℕ) :
    0 < idealSiteBoxRadius α degree := by
  have h := partitionedIdealRadius_nonneg α degree
  unfold idealSiteBoxRadius
  positivity

theorem idealSiteBoxRadius_buffer_le_exp (α : Type*) [Fintype α] (degree : ℕ) :
    2 * idealSiteBoxRadius α degree ≤
      Real.exp (((degree : ℝ) + 2) * Fintype.card α + 3) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ Fintype.card α ≤ Real.exp (Fintype.card α : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card α := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one]
  unfold idealSiteBoxRadius
  calc
    _ ≤ Real.exp 1 * (Real.exp (Fintype.card α : ℝ) *
        Real.exp (((degree : ℝ) + 1) * Fintype.card α + 2)) := by
      have hr0 : 0 ≤ partitionedIdealRadius α degree + 1 := by
        have h := partitionedIdealRadius_nonneg α degree
        linarith
      exact mul_le_mul htwo
        (mul_le_mul hp (partitionedIdealRadius_add_one_le_exp α degree) hr0 (Real.exp_pos _).le)
        (mul_nonneg (by positivity) hr0) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

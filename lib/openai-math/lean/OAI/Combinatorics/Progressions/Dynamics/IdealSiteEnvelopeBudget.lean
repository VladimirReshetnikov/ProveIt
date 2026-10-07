import OAI.Combinatorics.Progressions.Geometry.IdealSiteBoxRadius

namespace OAI

section

namespace Erdos3

noncomputable def idealSiteEnvelopeRadius (α : Type*) [Fintype α] (degree : ℕ) : ℝ :=
  (2 : ℝ) ^ Fintype.card α * (2 * idealSiteBoxRadius α degree)

theorem idealSiteEnvelopeRadius_pos (α : Type*) [Fintype α] (degree : ℕ) :
    0 < idealSiteEnvelopeRadius α degree := by
  have h := idealSiteBoxRadius_pos α degree
  unfold idealSiteEnvelopeRadius
  positivity

theorem idealSiteEnvelopeRadius_le_exp (α : Type*) [Fintype α] (degree : ℕ) :
    idealSiteEnvelopeRadius α degree ≤
      Real.exp (((degree : ℝ) + 3) * Fintype.card α + 3) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ Fintype.card α ≤ Real.exp (Fintype.card α : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card α := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one]
  unfold idealSiteEnvelopeRadius
  calc
    _ ≤ Real.exp (Fintype.card α : ℝ) *
        Real.exp (((degree : ℝ) + 2) * Fintype.card α + 3) :=
      mul_le_mul hp (idealSiteBoxRadius_buffer_le_exp α degree)
        (mul_nonneg (by norm_num) (idealSiteBoxRadius_pos α degree).le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem idealSiteEnvelopeRadius_volume_le_exp (α : Type*) [Fintype α] (degree N : ℕ) :
    (2 * idealSiteEnvelopeRadius α degree + 1) ^ N ≤
      Real.exp ((N : ℝ) * (((degree : ℝ) + 3) * Fintype.card α + 5)) := by
  let L : ℝ := ((degree : ℝ) + 3) * Fintype.card α + 3
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hT : idealSiteEnvelopeRadius α degree ≤ Real.exp L := idealSiteEnvelopeRadius_le_exp α degree
  have hunit : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hbase : 2 * idealSiteEnvelopeRadius α degree + 1 ≤ Real.exp (L + 2) := by
    calc
      _ ≤ 3 * Real.exp L := by linarith
      _ ≤ Real.exp 2 * Real.exp L := mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  calc
    _ ≤ (Real.exp (L + 2)) ^ N :=
      pow_le_pow_left₀ (by linarith [idealSiteEnvelopeRadius_pos α degree]) hbase N
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp only [L]
      ring

end Erdos3

end

end OAI

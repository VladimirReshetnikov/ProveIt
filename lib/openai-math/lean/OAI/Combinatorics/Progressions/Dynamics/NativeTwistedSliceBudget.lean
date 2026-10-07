import OAI.Combinatorics.Progressions.Estimates.NormalizedTwistSliceVariationPairCorrelation

namespace OAI

section

namespace Erdos3

theorem nativeTwistedSlice_freezing_error {p L mass : ℝ}
    (hp : 0 ≤ p) (_hL : 0 ≤ L) (hLp : L ≤ Real.exp p)
    (hmass : 0 ≤ mass) (hmass1 : mass ≤ 1) :
    Real.exp p * (2 * L * (Real.exp (-(2 * (2 * p + 2))) / 4) * mass) ≤
      Real.exp (-p) / 4 := by
  have h2 : (2 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp 4
    linarith
  have hsmall : 2 * Real.exp (-4) ≤ 1 := by
    rw [Real.exp_neg]
    exact (mul_inv_le_iff₀ (Real.exp_pos 4)).mpr (by simpa using h2)
  calc
    _ ≤ Real.exp p * (2 * Real.exp p * (Real.exp (-(2 * (2 * p + 2))) / 4) * 1) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLp (by norm_num)) (by positivity)
      · exact hmass1
      · exact hmass
      · positivity
    _ = 2 * Real.exp (-4) * Real.exp (-2 * p) / 4 := by
      rw [mul_one]
      have he : Real.exp p * Real.exp p * Real.exp (-(2 * (2 * p + 2))) =
          Real.exp (-4) * Real.exp (-2 * p) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = 2 * (Real.exp p * Real.exp p * Real.exp (-(2 * (2 * p + 2)))) / 4 := by ring
        _ = _ := by rw [he]; ring
    _ ≤ Real.exp (-p) / 4 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      calc
        _ ≤ 1 * Real.exp (-2 * p) := mul_le_mul_of_nonneg_right hsmall (Real.exp_nonneg _)
        _ ≤ Real.exp (-p) := by rw [one_mul]; exact Real.exp_le_exp.mpr (by linarith)

theorem nativeTwistedSlice_bias_precision (p : ℝ) :
    Real.exp (-(p + 2)) ≤ Real.exp (-p) / 4 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; norm_num at this ⊢; exact this
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 2
    norm_num only [pow_two, mul_comm, ← Real.exp_add] at h
    exact h
  rw [show -(p + 2) = -p - 2 by ring, Real.exp_sub]
  exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) hfour

end Erdos3

end

end OAI

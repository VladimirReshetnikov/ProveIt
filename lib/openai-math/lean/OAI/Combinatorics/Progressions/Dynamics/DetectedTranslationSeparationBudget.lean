import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3

theorem detectedTranslationSeparation_budget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ (p + 3) ^ 5 ∧
      (p + 3) ^ 3 ≤ (p + 3) ^ 5 ∧
      (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp ((p + 3) ^ 5) := by
  have hbase : 1 ≤ p + 3 := by linarith
  have hlinear : p + 3 ≤ (p + 3) ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : 1 ≤ 5)
  refine ⟨(by linarith), pow_le_pow_right₀ hbase (by decide : 3 ≤ 5), ?_⟩
  apply (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4)).trans
  apply Real.exp_le_exp.mpr
  have hfour : (p + 2) ^ 4 ≤ (p + 3) ^ 4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hone : 1 ≤ (p + 3) ^ 4 := one_le_pow₀ hbase
  calc
    (p + 2) ^ 4 + 1 ≤ 2 * (p + 3) ^ 4 := by linarith
    _ ≤ (p + 3) * (p + 3) ^ 4 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (p + 3) ^ 5 := by ring

end Erdos3

end

end OAI

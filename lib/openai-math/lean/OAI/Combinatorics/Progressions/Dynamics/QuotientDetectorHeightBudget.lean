import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3

theorem quotient_detector_height_budget {p : ℝ} (hp : 0 ≤ p) :
    1 ≤ ⌈Real.exp ((p + 2) ^ 7)⌉₊ ∧
    (⌈Real.exp ((p + 2) ^ 7)⌉₊ : ℝ) ≤ Real.exp ((p + 2) ^ 8) := by
  refine ⟨one_le_ceil_exp _, ?_⟩
  apply (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 7)).trans
  apply Real.exp_le_exp.mpr
  have hpow : 1 ≤ (p + 2) ^ 7 := one_le_pow₀ (by linarith)
  calc
    (p + 2) ^ 7 + 1 ≤ (p + 2) ^ 7 + (p + 2) ^ 7 := by linarith
    _ = (p + 2) ^ 7 * 2 := by ring
    _ ≤ (p + 2) ^ 7 * (p + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (p + 2) ^ 8 := (pow_succ (p + 2) 7).symm

theorem rationalHeightLE_ceil_exp_of_entries {q : ℚ} {r : ℝ}
    (hq : (q.num.natAbs : ℝ) ≤ Real.exp r ∧ (q.den : ℝ) ≤ Real.exp r) :
    RationalHeightLE q ⌈Real.exp r⌉₊ :=
  ⟨Nat.cast_le.mp (hq.1.trans (Nat.le_ceil _)),
    Nat.cast_le.mp (hq.2.trans (Nat.le_ceil _))⟩

end Erdos3

end

end OAI

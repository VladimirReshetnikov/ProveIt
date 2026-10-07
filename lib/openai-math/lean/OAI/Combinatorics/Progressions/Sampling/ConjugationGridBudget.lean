import OAI.Combinatorics.Progressions.Dynamics.CandidateFrontSourceLossBudget

namespace OAI

section

namespace Erdos3

theorem conjugation_grid_allowance_le_exp (K s l D q : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hD : (D : ℝ) ≤ Real.exp ((p + K) ^ K))
    (hq : (q : ℝ) ≤ Real.exp p) :
    ((l * D * q ^ s : ℕ) : ℝ) ≤
      Real.exp ((p + (K + s + 5)) ^ (K + s + 5)) := by
  let J := K + s + 5
  let t := p + J
  have ht : 2 ≤ t := by
    dsimp [t, J]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) s]
  have hp_le : p ≤ t := by dsimp [t]; have := Nat.cast_nonneg (α := ℝ) J; linarith
  have hs_le : (s : ℝ) + 1 ≤ t := by dsimp [t, J]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) K]
  have hbig : (p + K) ^ K ≤ t ^ (J - 1) := by
    apply (pow_le_pow_left₀ (by positivity : 0 ≤ p + K) (show p + K ≤ t by
      dsimp [t, J]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]) K).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [J]; omega)
  have hsmall : ((s : ℝ) + 1) * p ≤ t ^ (J - 1) := by
    apply (show ((s : ℝ) + 1) * p ≤ t ^ 2 by
      simpa only [pow_two] using mul_le_mul hs_le hp_le hp (by linarith : 0 ≤ t)).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [J]; omega)
  have hqpow : (q : ℝ) ^ s ≤ Real.exp ((s : ℝ) * p) := by
    simpa only [← Real.exp_nat_mul] using pow_le_pow_left₀ (Nat.cast_nonneg q) hq s
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp ((p + K) ^ K) * Real.exp ((s : ℝ) * p) :=
      mul_le_mul (mul_le_mul hl hD (by positivity) (by positivity)) hqpow (by positivity) (by positivity)
    _ = Real.exp ((p + K) ^ K + ((s : ℝ) + 1) * p) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (t ^ J) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ 2 * t ^ (J - 1) := by linarith
        _ ≤ t * t ^ (J - 1) := mul_le_mul_of_nonneg_right ht (by positivity)
        _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by dsimp [J]; omega)]
    _ = _ := by simp [t, J]

end Erdos3

end

end OAI

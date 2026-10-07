import OAI.Combinatorics.Progressions.Estimates.NormalizedDeterminantCutoff

namespace OAI

section

namespace Erdos3

theorem nat_mul_factorial_le_exp_square (n : ℕ) :
    ((n * n.factorial : ℕ) : ℝ) ≤ Real.exp (((n : ℝ) + 1) ^ 2) := by
  have hn : (n : ℝ) ≤ Real.exp (n : ℝ) := by
    have h := Real.add_one_le_exp (n : ℝ)
    linarith
  have hf : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast n.factorial_le_pow
  have hp : (n : ℝ) ^ n ≤ Real.exp ((n : ℝ) * n) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hn n
  calc
    _ = (n : ℝ) * n.factorial := by push_cast; rfl
    _ ≤ Real.exp (n : ℝ) * Real.exp ((n : ℝ) * n) :=
      mul_le_mul hn (hf.trans hp) (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) + (n : ℝ) * n) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

theorem determinantCutoff_lip_le_exp (n : ℕ) {κ K : ℝ}
    (hκ : 0 < κ) (hK : κ⁻¹ ≤ Real.exp K) :
    (2 / κ) * ((n * n.factorial : ℕ) : ℝ) ≤
      Real.exp (K + ((n : ℝ) + 1) ^ 2 + 1) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  calc
    _ = (2 * κ⁻¹) * ((n * n.factorial : ℕ) : ℝ) := by rw [div_eq_mul_inv]
    _ ≤ (Real.exp 1 * Real.exp K) * Real.exp (((n : ℝ) + 1) ^ 2) := by
      gcongr
      exact nat_mul_factorial_le_exp_square n
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem spatialMatrixBlockCutoff_lip_exp_budget {n : ℕ} (hn : 0 < n)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    (2 / spatialMatrixBlockThreshold n η) * ((n * n.factorial : ℕ) : ℝ) ≤
      Real.exp (smoothMatrixBlockThresholdLogBudget (2 * n * n) n 2 E +
        ((n : ℝ) + 1) ^ 2 + 1) :=
  determinantCutoff_lip_le_exp n (spatialMatrixBlockThreshold_pos hn hη)
    (spatialMatrixBlockThreshold_inverse_le_exp hn hη hE hηb)

end Erdos3

end

end OAI

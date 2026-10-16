import GowersSzemeredi.Proofs18FejerReciprocalBudgets
import GowersSzemeredi.Proofs18FejerCubicTwistedDiscrepancy
import GowersSzemeredi.Proofs18QuadraticNumericalConstant

/-! Conventional double-exponential modulus bounds for every local prime
model and the assembled cubic twisted discrepancy partition. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

set_option exponentiation.threshold 512 in
/-- The actual local quadratic inverse threshold is single exponential in
an explicit fixed power of the original cubic uniformity parameter. -/
theorem quadraticExponentialThreshold_fejer_le_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    quadraticExponentialThreshold (fejerCubicLocalQuadraticParameter alpha) ≤
      Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 323)) := by
  let x := 2 / alpha
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have h1 := section5LocalRefinementConstant_pos 1 1
  have hC : 4 + 6 * section5LocalRefinementConstant 2 1 ≤ x ^ ((2 : Nat) ^ 322) := by
    have hc : 4 + 6 * section5LocalRefinementConstant 2 1 ≤ quadraticIterationLogBudgetConstant + 1 := by
      unfold quadraticIterationLogBudgetConstant
      linarith only [h1]
    exact (hc.trans quadraticIterationLogBudgetConstant_upper).trans
      (pow_le_pow_left₀ (by norm_num) hx _)
  have ha := fejerCubicLocalQuadraticParameter_pos hα
  have hbase := two_div_fejerCubicLocalQuadraticParameter_le_power hα hαone
  have hP := pow_le_pow_left₀ (by positivity : 0 ≤ 2 / fejerCubicLocalQuadraticParameter alpha)
    hbase (12380 * 2048 + 24744)
  rw [← pow_mul] at hP
  unfold quadraticExponentialThreshold
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ x ^ ((2 : Nat) ^ 322) * x ^ (((2 : Nat) ^ 43 + 1) * (12380 * 2048 + 24744)) :=
      mul_le_mul hC hP (by positivity) (by positivity)
    _ = x ^ ((2 : Nat) ^ 322 + ((2 : Nat) ^ 43 + 1) * (12380 * 2048 + 24744)) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num)

end LeanProofs.GowersSzemeredi

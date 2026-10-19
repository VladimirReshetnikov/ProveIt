import GowersSzemeredi.Proofs13GeometricThresholdEnvelope
import GowersSzemeredi.Proofs13FejerOddSquare

/-! The complete cubic Fourier inverse theorem at a conventional explicit
double-exponential modulus threshold.

`theorem_13_12_fejer_double_exponential` is in
`Proofs13FourierThresholdEnvelopeSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem real_le_double_exp (x : Real) : x ≤ Real.exp (Real.exp x) := by
  have h : x ≤ Real.exp x := by have h := Real.add_one_le_exp x; linarith only [h]
  exact h.trans (Real.exp_le_exp.mpr h)

theorem section13FourierThreshold_le_double_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    section13FourierThreshold alpha ≤ Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 54))) := by
  have ht : 1 ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  unfold section13FourierThreshold
  apply max_le
  · exact (section13FrequencyGraphThreshold_le_power hα hαone).trans
      ((pow_le_pow_right₀ ht (by norm_num : (2 : Nat) ^ 37 ≤ (2 : Nat) ^ 54)).trans
        (real_le_double_exp _))
  · exact section13_fejer_geometric_threshold_le_double_exp hα hαone

/-- The same modulus bound suffices for the odd-square localization input. -/
theorem section13FejerOddSquareThreshold_le_double_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    section13FejerOddSquareThreshold alpha ≤ Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 54))) := by
  let x := 2 / alpha
  let A := x ^ ((2 : Nat) ^ 53)
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hA4 : 4 ≤ A := le_trans (by nlinarith only [hx] : (4 : Real) ≤ x ^ 2)
    (pow_le_pow_right₀ (by linarith only [hx]) (by norm_num))
  have hA0 : 0 ≤ A := (by norm_num : (0 : Real) ≤ 4).trans hA4
  have heI : ((1 / 2 : Real) ^ A)⁻¹ ≤ Real.exp (1 * A) := by
    rw [one_mul, one_div, Real.inv_rpow (by norm_num), inv_inv]
    exact two_rpow_le_exp hA0
  have hpower := positivePowerThreshold_le_double_exp (C := 4) zero_lt_one (by positivity) hA0
    zero_le_one zero_le_one (by rw [one_mul]; linarith only [eight_le_exp_of_four_le hA4])
    (by rw [inv_one, one_mul]; exact Real.one_le_exp_iff.mpr hA0) heI
  have hinner : (1 + 1 + 1) * A ≤ x ^ ((2 : Nat) ^ 54) := by
    rw [show (2 : Nat) ^ 54 = 2 ^ 53 + 2 ^ 53 by norm_num, pow_add]
    exact mul_le_mul_of_nonneg_right ((by norm_num : (1 + 1 + 1 : Real) ≤ 4).trans hA4) hA0
  exact max_le (section13FourierThreshold_le_double_exp hα hαone)
    (hpower.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hinner)))

end LeanProofs.GowersSzemeredi

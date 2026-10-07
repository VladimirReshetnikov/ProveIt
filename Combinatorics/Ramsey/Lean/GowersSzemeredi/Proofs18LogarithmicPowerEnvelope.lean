import GowersSzemeredi.Proofs13ThresholdExponentialEnvelope

/-! Keep fixed powers inside logarithmic budgets rather than carrying their
enormous numerical exponents into a second exponential. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Taking one logarithmic budget turns a power exponent 2^n into n+1.
This estimate is uniform over the entire range x>=2. -/
theorem pow_two_pow_le_exp_pow_succ {x : Real} (hx : 2 ≤ x) (n : Nat) :
    x ^ ((2 : Nat) ^ n) ≤ Real.exp (x ^ (n + 1)) := by
  have hx0 : 0 < x := by linarith only [hx]
  apply (Real.log_le_iff_le_exp (pow_pos hx0 _)).mp
  rw [Real.log_pow]
  have hc : (((2 : Nat) ^ n : Nat) : Real) ≤ x ^ n := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using pow_le_pow_left₀ (by norm_num) hx n
  calc
    _ ≤ x ^ n * x := mul_le_mul hc (Real.log_le_self hx0.le)
      (Real.log_nonneg (by linarith only [hx])) (pow_nonneg hx0.le _)
    _ = _ := (pow_succ x n).symm

/-- A double-exponential numerator and single-exponential inverse exponent
still require only a double-exponential positive-power threshold. -/
theorem positivePowerThreshold_one_le_double_exp
    {C e A B : Real} (he : 0 ≤ e)
    (hC : C ≤ Real.exp (Real.exp A)) (heI : e⁻¹ ≤ Real.exp B) :
    positivePowerThreshold C 1 e ≤ Real.exp (Real.exp (A + B)) := by
  have h := positivePowerThreshold_le_exp zero_lt_one he
    (by positivity : 0 ≤ Real.exp A + 0) hC
    (by norm_num : (1 : Real)⁻¹ ≤ Real.exp 0) heI
  simpa only [add_zero, ← Real.exp_add] using h

end LeanProofs.GowersSzemeredi

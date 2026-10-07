import GowersSzemeredi.Proofs18DensityIteration

/-! A closed exponential upper bound for the backward length recursion. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The backward thresholds grow at most exponentially in a geometric
sequence. This estimate permits all positive factors and exponents. -/
theorem densityIterationThreshold_le_exp {T c rho A q : Real}
    (hc : 0 < c) (hρ : 0 < rho)
    (hA : 1 + Real.log (max 1 T) + |Real.log c| ≤ A)
    (hq : 1 ≤ q) (hρq : rho⁻¹ ≤ q) (n : Nat) :
    densityIterationThreshold T c rho n ≤ Real.exp (A * (2 * q) ^ n) := by
  have hM : 0 < max 1 T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlogM : 0 ≤ Real.log (max 1 T) := Real.log_nonneg (le_max_left _ _)
  have hApos : 0 < A := by linarith [abs_nonneg (Real.log c)]
  have hlogMA : Real.log (max 1 T) ≤ A := by linarith [abs_nonneg (Real.log c)]
  have habs : |Real.log c| ≤ A := by linarith
  have hbase : 1 ≤ 2 * q := by linarith
  have hMexp : max 1 T ≤ Real.exp A := (Real.log_le_iff_le_exp hM).mp hlogMA
  induction n with
  | zero => simpa [densityIterationThreshold] using hMexp
  | succ n ih =>
    change max (max 1 T) ((densityIterationThreshold T c rho n / c) ^ rho⁻¹) ≤ _
    apply max_le
    · apply hMexp.trans
      apply Real.exp_le_exp.mpr
      exact le_mul_of_one_le_right hApos.le (one_le_pow₀ hbase)
    · have hn : 0 < densityIterationThreshold T c rho n := lt_of_lt_of_le (by norm_num)
        (densityIterationThreshold_one_le T c rho n)
      rw [Real.rpow_def_of_pos (div_pos hn hc), Real.log_div hn.ne' hc.ne']
      apply Real.exp_le_exp.mpr
      have hlog := (Real.log_le_iff_le_exp hn).mpr ih
      have hpow : 1 ≤ (2 * q) ^ n := one_le_pow₀ hbase
      have hmul : A ≤ A * (2 * q) ^ n := le_mul_of_one_le_right hApos.le hpow
      have hdiff : Real.log (densityIterationThreshold T c rho n) - Real.log c ≤
          2 * A * (2 * q) ^ n := by linarith [neg_le_abs (Real.log c)]
      calc
        _ ≤ (2 * A * (2 * q) ^ n) * rho⁻¹ :=
          mul_le_mul_of_nonneg_right hdiff (inv_nonneg.mpr hρ.le)
        _ ≤ (2 * A * (2 * q) ^ n) * q :=
          mul_le_mul_of_nonneg_left hρq (by positivity)
        _ = _ := by rw [pow_succ]; ring

def densityIterationClosedThreshold (T c rho : Real) (n : Nat) : Real :=
  Real.exp ((1 + Real.log (max 1 T) + |Real.log c|) * (2 * max 1 rho⁻¹) ^ n)

theorem densityIterationThreshold_le_closed {T c rho : Real}
    (hc : 0 < c) (hρ : 0 < rho) (n : Nat) :
    densityIterationThreshold T c rho n ≤ densityIterationClosedThreshold T c rho n :=
  densityIterationThreshold_le_exp hc hρ le_rfl (le_max_left _ _) (le_max_right _ _) n

end LeanProofs.GowersSzemeredi

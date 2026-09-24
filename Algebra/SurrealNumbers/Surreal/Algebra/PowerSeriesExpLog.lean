import Mathlib.RingTheory.PowerSeries.Log

/-!
# Formal exponential and logarithm are inverse under substitution

These are algebraic identities of formal power series over a characteristic-zero
field. No convergence or topology is used.
-/

namespace Surreal.FormalPowerSeries

open PowerSeries
open scoped PowerSeries

noncomputable section

variable (K : Type*) [Field K] [CharZero K]

/-- The formal logarithmic derivative is the inverse of `1 + X`. -/
theorem derivative_log_mul_one_add_X :
    derivative K (log K) * (1 + X) = 1 := by
  rw [mul_add, mul_one]
  ext n
  cases n with
  | zero => simp [deriv_log]
  | succ n =>
    simp only [map_add, coeff_succ_mul_X, deriv_log, coeff_mk, coeff_one,
      Nat.succ_ne_zero, ↓reduceIte]
    rw [pow_succ, map_mul, map_neg, map_one]
    ring

/-- `log(exp(X)) = X` as a formal substitution identity. -/
theorem log_subst_exp_sub_one : (log K).subst (exp K - 1) = X := by
  apply derivative.ext
  · rw [derivative_subst K HasSubst.exp_sub_one, map_sub,
      derivative_exp, Derivation.map_one_eq_zero, sub_zero, derivative_X]
    have h := congrArg (substAlgHom (R := K) (a := exp K - 1) HasSubst.exp_sub_one)
      (derivative_log_mul_one_add_X K)
    simpa only [map_mul, map_add, map_one, coe_substAlgHom,
      subst_X HasSubst.exp_sub_one, add_sub_cancel] using h
  · simpa only [constantCoeff_X, ← constantCoeff_eq] using
      (constantCoeff_subst_eq_zero
        (show MvPowerSeries.constantCoeff (exp K - 1) = 0 from by
          change constantCoeff (exp K - 1) = 0
          simp) (log K) constantCoeff_log)

/-- `exp(log(1+X)) = 1+X` as a formal substitution identity. -/
theorem exp_subst_log : (exp K).subst (log K) = 1 + X := by
  let P := exp K - 1
  have hP : P.constantCoeff = 0 := by simp [P]
  have hPu : IsUnit (P.coeff 1) := by simp [P]
  let Q := P.substInvOfIsUnit hPu
  have hQ : HasSubst Q := HasSubst.substInvOfIsUnit P hPu
  have hPQ : P.subst Q = X := subst_substInvOfIsUnit_right P hP hPu
  have hlog : log K = Q := by
    have h := congrArg (fun f : PowerSeries K => f.subst Q)
      (log_subst_exp_sub_one K)
    rw [subst_comp_subst_apply HasSubst.exp_sub_one hQ,
      show (exp K - 1).subst Q = X from hPQ, X_subst, subst_X hQ] at h
    exact h
  have h := hPQ
  rw [← hlog, subst_sub HasSubst.log] at h
  have hone : (1 : PowerSeries K).subst (log K) = 1 := by
    rw [← coe_substAlgHom HasSubst.log, map_one]
  rw [hone] at h
  linear_combination h

end
end Surreal.FormalPowerSeries

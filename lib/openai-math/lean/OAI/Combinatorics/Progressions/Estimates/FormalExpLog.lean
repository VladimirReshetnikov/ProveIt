import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open PowerSeries

theorem formalSeries_eq_of_derivative_eq {f g : PowerSeries ℚ}
    (hd : derivative f = derivative g) (hc : constantCoeff f = constantCoeff g) :
    f = g := by
  ext n
  cases n with
  | zero => simpa only [coeff_zero_eq_constantCoeff] using hc
  | succ n =>
    have h := congrArg (coeff n) hd
    simp only [coeff_derivative] at h
    exact mul_right_cancel₀ (by positivity : (n : ℚ) + 1 ≠ 0) h

theorem formal_log_derivative_mul : derivative (log ℚ) * (1 + X) = (1 : PowerSeries ℚ) := by
  rw [derivative_log, mul_add, mul_one]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [map_add, coeff_succ_mul_X, coeff_mk, coeff_one, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ite_false, pow_succ]
    simp

theorem formal_log_derivative_subst {f : PowerSeries ℚ} (hf : HasSubst f) :
    (derivative (log ℚ)).subst f * (1 + f) = 1 := by
  have h := congrArg (substAlgHom hf) formal_log_derivative_mul
  simpa only [map_mul, map_add, map_one, substAlgHom_X, coe_substAlgHom] using h

theorem formal_log_exp : (log ℚ).subst (exp ℚ - 1) = (X : PowerSeries ℚ) := by
  apply formalSeries_eq_of_derivative_eq
  · rw [derivative_subst HasSubst.exp_sub_one, derivative_X]
    have hd : derivative (exp ℚ - 1) = exp ℚ := by simp [derivative_exp]
    rw [hd]
    have hadd : (1 : PowerSeries ℚ) + (exp ℚ - 1) = exp ℚ := by abel
    simpa only [hadd] using
      formal_log_derivative_subst (f := exp ℚ - 1) HasSubst.exp_sub_one
  · have h := constantCoeff_logOf (f := exp ℚ) constantCoeff_exp
    simpa only [logOf_eq, constantCoeff_X] using h

theorem formal_exp_sub_one_log : (exp ℚ - 1).subst (log ℚ) = (X : PowerSeries ℚ) := by
  apply subst_eq_X_of_subst_eq_X (log ℚ) constantCoeff_log
    (by rw [coeff_one_log]; exact isUnit_one) HasSubst.exp_sub_one
  exact formal_log_exp

theorem formal_exp_log : (exp ℚ).subst (log ℚ) = (1 + X : PowerSeries ℚ) := by
  have h := formal_exp_sub_one_log
  rw [subst_sub HasSubst.log] at h
  have hone : (1 : PowerSeries ℚ).subst (log ℚ) = 1 := by
    rw [← coe_substAlgHom HasSubst.log, map_one]
  rw [hone] at h
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

end Erdos3

end

end OAI

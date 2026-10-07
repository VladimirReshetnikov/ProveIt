/- Modified for ProveIt: supply the explicit coefficient ring to the Lean
4.32 power-series derivative API, use deriv_log, and prove the inverse
substitution step with substInvOfIsUnit. Mathematical statements unchanged. -/
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open PowerSeries

theorem formalSeries_eq_of_derivative_eq {f g : PowerSeries ℚ}
    (hd : derivative ℚ f = derivative ℚ g) (hc : constantCoeff f = constantCoeff g) :
    f = g := by
  ext n
  cases n with
  | zero => simpa only [coeff_zero_eq_constantCoeff] using hc
  | succ n =>
    have h := congrArg (coeff n) hd
    simp only [coeff_derivative] at h
    exact mul_right_cancel₀ (by positivity : (n : ℚ) + 1 ≠ 0) h

theorem formal_log_derivative_mul : derivative ℚ (log ℚ) * (1 + X) = (1 : PowerSeries ℚ) := by
  rw [deriv_log, mul_add, mul_one]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [map_add, coeff_succ_mul_X, coeff_mk, coeff_one, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ite_false, pow_succ]
    simp

theorem formal_log_derivative_subst {f : PowerSeries ℚ} (hf : HasSubst f) :
    (derivative ℚ (log ℚ)).subst f * (1 + f) = 1 := by
  have h := congrArg (substAlgHom hf) formal_log_derivative_mul
  simpa only [map_mul, map_add, map_one, substAlgHom_X, coe_substAlgHom] using h

theorem formal_log_exp : (log ℚ).subst (exp ℚ - 1) = (X : PowerSeries ℚ) := by
  apply formalSeries_eq_of_derivative_eq
  · rw [derivative_subst ℚ HasSubst.exp_sub_one, derivative_X]
    have hd : derivative ℚ (exp ℚ - 1) = exp ℚ := by simp [derivative_exp]
    rw [hd]
    have hadd : (1 : PowerSeries ℚ) + (exp ℚ - 1) = exp ℚ := by abel
    simpa only [hadd] using
      formal_log_derivative_subst (f := exp ℚ - 1) HasSubst.exp_sub_one
  · have h := constantCoeff_logOf (f := exp ℚ) constantCoeff_exp
    simpa only [logOf_eq, constantCoeff_X] using h

theorem formal_exp_sub_one_log : (exp ℚ - 1).subst (log ℚ) = (X : PowerSeries ℚ) := by
  have hu : IsUnit (coeff 1 (log ℚ)) := by rw [coeff_one_log]; exact isUnit_one
  let R : PowerSeries ℚ := (log ℚ).substInvOfIsUnit hu
  have hleft : R.subst (log ℚ) = X :=
    subst_substInvOfIsUnit_left (log ℚ) constantCoeff_log hu
  have heq : exp ℚ - 1 = R := by
    calc
      _ = (X : PowerSeries ℚ).subst (exp ℚ - 1) := (subst_X HasSubst.exp_sub_one).symm
      _ = PowerSeries.subst (exp ℚ - 1) (PowerSeries.subst (log ℚ) R) := by rw [hleft]
      _ = PowerSeries.subst (PowerSeries.subst (exp ℚ - 1) (log ℚ)) R :=
        subst_comp_subst_apply HasSubst.log HasSubst.exp_sub_one R
      _ = R := by rw [formal_log_exp, X_subst]
  rw [heq]
  exact hleft

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

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Elementary double-exponential estimates shared by the uniform and
specialized discrepancy arguments. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem exp_exp_sq_le {Z : Real} :
    Real.exp (Real.exp Z) * Real.exp (Real.exp Z) ≤ Real.exp (Real.exp (Z + 1)) := by
  rw [← Real.exp_add, Real.exp_add Z 1]
  apply Real.exp_le_exp.mpr
  have he2 : (2 : Real) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : Real); linarith only [this]
  have h0 := (Real.exp_pos Z).le
  nlinarith only [he2, h0]

theorem pow_add_pow_le {X : Real} {a b : Nat} (hX : 2 ≤ X) (hab : b ≤ a) :
    X ^ a + X ^ b ≤ X ^ (a + 1) := by
  have h := pow_le_pow_right₀ (le_trans (by norm_num) hX) hab
  have h0 := pow_nonneg (le_trans (by norm_num) hX) a
  rw [pow_succ]
  nlinarith only [h, h0, hX]

theorem le_exp_exp_of_le_exp {x Y : Real} (hx : x ≤ Real.exp Y) : x ≤ Real.exp (Real.exp Y) :=
  hx.trans (Real.exp_le_exp.mpr ((Real.add_one_le_exp Y).trans' (by linarith only)))

theorem section18_exp_le_two_rpow {x : Real} (hx : 0 ≤ x) :
    Real.exp x ≤ (2 : Real) ^ (2 * x) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : Real) < 2)]
  apply Real.exp_le_exp.mpr
  have hh := Real.log_two_gt_d9
  nlinarith

end LeanProofs.GowersSzemeredi

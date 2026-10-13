import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Elementary exponential product bounds shared by the class step and
length-six threshold arguments. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem exp_pow_sq_le {X : Real} (hX : 2 ≤ X) (m : Nat) :
    Real.exp (X ^ m) * Real.exp (X ^ m) ≤ Real.exp (X ^ (m + 1)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := pow_nonneg (le_trans (by norm_num) hX) m
  calc X ^ m + X ^ m = 2 * X ^ m := by ring
    _ ≤ X * X ^ m := mul_le_mul_of_nonneg_right hX h
    _ = X ^ (m + 1) := (pow_succ' X m).symm

theorem exp_mul_le {X a b : Real} {m : Nat} (hX : 2 ≤ X) (hb0 : 0 ≤ b)
    (ha : a ≤ Real.exp (X ^ m)) (hb : b ≤ Real.exp (X ^ m)) : a * b ≤ Real.exp (X ^ (m + 1)) :=
  (mul_le_mul ha hb hb0 (Real.exp_pos _).le).trans (exp_pow_sq_le hX m)

end LeanProofs.GowersSzemeredi

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

/-- Convert a natural double exponential to a base-two tower using a linear margin. -/
theorem exp_exp_le_two_rpow_two_rpow {x y : Real} (hx : 0 ≤ x) (hxy : 1 + 2 * x ≤ y) :
    Real.exp (Real.exp x) ≤ (2 : Real) ^ ((2 : Real) ^ y) := by
  apply (section18_exp_le_two_rpow (Real.exp_pos _).le).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  calc
    2 * Real.exp x ≤ 2 * (2 : Real) ^ (2 * x) :=
      mul_le_mul_of_nonneg_left (section18_exp_le_two_rpow hx) (by norm_num)
    _ = (2 : Real) ^ (1 + 2 * x) := by
      rw [Real.rpow_add (by norm_num : (0 : Real) < 2), Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hxy

/-- Two spare powers of a base at least two absorb the double-exponential conversion. -/
theorem exp_exp_pow_le_two_rpow_two_rpow {u : Real} {q E : Nat}
    (hu : 2 ≤ u) (hqE : q + 2 ≤ E) :
    Real.exp (Real.exp (u ^ q)) ≤ (2 : Real) ^ ((2 : Real) ^ (u ^ E)) := by
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu
  apply exp_exp_le_two_rpow_two_rpow (pow_nonneg hu0 _)
  calc
    1 + 2 * u ^ q ≤ u ^ q * 4 := by linarith only [one_le_pow₀ hu1 (n := q)]
    _ ≤ u ^ q * u ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hu] : (4 : Real) ≤ u ^ 2) (pow_nonneg hu0 _)
    _ = u ^ (q + 2) := (pow_add u q 2).symm
    _ ≤ _ := pow_le_pow_right₀ hu1 hqE

end LeanProofs.GowersSzemeredi

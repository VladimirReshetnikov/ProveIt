import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Odd-length rounding and the elementary Fourier-exponent bounds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Rounding down to an odd integer loses at most a factor two above four. -/
theorem exists_odd_nat_between_half {x : Real} (hx : 4 ≤ x) :
    ∃ m : Nat, Odd m ∧ 0 < m ∧ x / 2 ≤ m ∧ (m : Real) ≤ x := by
  let n := Nat.floor x
  have hn : 4 ≤ n := Nat.le_floor hx
  let m := 2 * ((n - 1) / 2) + 1
  have hmod := Nat.mod_lt (n - 1) (by omega : 0 < 2)
  have hdiv := Nat.div_add_mod (n - 1) 2
  have hmn : m ≤ n := by dsimp [m]; omega
  have hnm : n ≤ m + 1 := by dsimp [m]; omega
  have hnmR : (n : Real) ≤ (m : Real) + 1 := by exact_mod_cast hnm
  have hxupper : x < (n : Real) + 1 := Nat.lt_floor_add_one x
  refine ⟨m, ⟨(n - 1) / 2, rfl⟩, by dsimp [m]; omega, ?_, ?_⟩
  · linarith only [hx, hxupper, hnmR]
  · exact (by exact_mod_cast hmn : (m : Real) ≤ n).trans (Nat.floor_le (by linarith only [hx]))

/-- The explicit Fourier extraction exponent lies in (0,1/2]. -/
theorem section13_explicit_exponent_bounds {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    0 < (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88)) ∧
      (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88)) ≤ 1 / 2 := by
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  have ht : (1 : Real) ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hexp := one_le_pow₀ ht (n := (2 : Nat) ^ 88)
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
    (by norm_num : (0 : Real) < 1 / 2) (by norm_num : (1 / 2 : Real) ≤ 1) hexp

end LeanProofs.GowersSzemeredi

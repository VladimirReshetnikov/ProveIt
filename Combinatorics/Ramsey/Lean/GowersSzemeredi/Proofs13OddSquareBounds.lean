import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Odd-length rounding and the elementary Fourier-exponent bounds.

`section13_explicit_exponent_bounds` is in `Proofs13OddSquareBoundsSide`,
outside the final route. -/
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
  have hmn : m ≤ n := by dsimp [m]; omega
  have hnm : n ≤ m + 1 := by dsimp [m]; omega
  have hnmR : (n : Real) ≤ (m : Real) + 1 := by exact_mod_cast hnm
  have hxupper : x < (n : Real) + 1 := Nat.lt_floor_add_one x
  refine ⟨m, ⟨(n - 1) / 2, rfl⟩, by dsimp [m]; omega, ?_, ?_⟩
  · linarith only [hx, hxupper, hnmR]
  · exact (by exact_mod_cast hmn : (m : Real) ≤ n).trans (Nat.floor_le (by linarith only [hx]))

end LeanProofs.GowersSzemeredi

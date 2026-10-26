import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option Elab.async false

/-! An elementary integer descent for the zero norm of A²-1.
The nonzero second coordinate and A>=2 are essential premises. -/
namespace DiophantineConsistency.NearSquareNormZero

private theorem no_zero_nat_y (A : ℤ) (hA : 2 ≤ A) :
    ∀ y : ℕ, 0 < y → ∀ x : ℤ, x ^ 2 - (A ^ 2 - 1) * (y : ℤ) ^ 2 ≠ 0 := by
  intro y
  induction y using Nat.strong_induction_on with
  | h y ih =>
      intro hy x hnorm
      have hyi : 0 < (y : ℤ) := by exact_mod_cast hy
      have hy2 : 0 < (y : ℤ) ^ 2 := sq_pos_of_pos hyi
      have hx : 0 ≤ |x| := abs_nonneg x
      have hn : |x| ^ 2 - (A ^ 2 - 1) * (y : ℤ) ^ 2 = 0 := by
        simpa only [sq_abs] using hnorm
      have hlay : 0 ≤ (A - 1) * (y : ℤ) := mul_nonneg (by omega) hyi.le
      have hay : 0 ≤ A * (y : ℤ) := mul_nonneg (by omega) hyi.le
      have hlower : (A - 1) * (y : ℤ) < |x| := by
        by_contra h
        have hle := le_of_not_gt h
        have hp := mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hlay hx)
        have hstrict : 0 < (2 * A - 2) * (y : ℤ) ^ 2 :=
          mul_pos (by omega) hy2
        nlinarith
      have hupper : |x| < A * (y : ℤ) := by
        by_contra h
        have hle := le_of_not_gt h
        have hp := mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hx hay)
        nlinarith
      let y' : ℤ := A * (y : ℤ) - |x|
      let x' : ℤ := A * |x| - (A ^ 2 - 1) * (y : ℤ)
      have hy' : 0 < y' := by dsimp [y']; omega
      have hsmall : y' < (y : ℤ) := by dsimp [y']; nlinarith
      have hnew : x' ^ 2 - (A ^ 2 - 1) * y' ^ 2 = 0 := by
        calc
          x' ^ 2 - (A ^ 2 - 1) * y' ^ 2 =
              |x| ^ 2 - (A ^ 2 - 1) * (y : ℤ) ^ 2 := by
                dsimp [x', y']; ring
          _ = 0 := hn
      have hcast : ((Int.toNat y' : ℕ) : ℤ) = y' := Int.toNat_of_nonneg hy'.le
      have hlt : Int.toNat y' < y := by
        exact_mod_cast (show ((Int.toNat y' : ℕ) : ℤ) < (y : ℤ) by
          rw [hcast]; exact hsmall)
      have hpos : 0 < Int.toNat y' := by
        exact_mod_cast (show (0 : ℤ) < ((Int.toNat y' : ℕ) : ℤ) by
          rw [hcast]; exact hy')
      exact ih (Int.toNat y') hlt hpos x' (by simpa only [hcast] using hnew)

/-- No nontrivial integer zero norm for the positive nonsquare A²-1. -/
theorem norm_ne_zero (A x y : ℤ) (hA : 2 ≤ A) (hy : y ≠ 0) :
    x ^ 2 - (A ^ 2 - 1) * y ^ 2 ≠ 0 := by
  have hpos : 0 < y.natAbs := Int.natAbs_pos.mpr hy
  simpa only [Int.natCast_natAbs, sq_abs] using no_zero_nat_y A hA y.natAbs hpos x

end DiophantineConsistency.NearSquareNormZero

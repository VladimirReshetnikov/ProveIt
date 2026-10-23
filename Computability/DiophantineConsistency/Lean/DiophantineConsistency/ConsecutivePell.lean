import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Negative Pell norms for two consecutive factors

For `n ≥ 2`, the norm `x² - n(n+1)y²` never equals `-1`.
The elementary descent multiplies by the norm-one unit
`(2n+1) + 2√(n(n+1))`. Its inverse takes the absolute values
of a hypothetical solution to another solution with a smaller positive
second coordinate. No continued-fraction theory is needed.
-/

namespace DiophantineConsistency.ConsecutivePell

private theorem no_negative_nat_y (n : ℤ) (hn : 2 ≤ n) :
    ∀ y : ℕ, ∀ x : ℤ, x ^ 2 - n * (n + 1) * (y : ℤ) ^ 2 ≠ -1 := by
  intro y
  induction y using Nat.strong_induction_on with
  | h y ih =>
      intro x hnorm
      have hy : 0 < (y : ℤ) := by
        by_contra hy
        have hy0 : (y : ℤ) = 0 := le_antisymm (le_of_not_gt hy) (Int.natCast_nonneg y)
        simp only [hy0, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at hnorm
        nlinarith [sq_nonneg x]
      have hx : 0 ≤ |x| := abs_nonneg x
      have hnorm' : |x| ^ 2 - n * (n + 1) * (y : ℤ) ^ 2 = -1 := by
        simpa only [sq_abs] using hnorm
      have hny : 0 ≤ n * (y : ℤ) := mul_nonneg (by omega) (by omega)
      have hnysq : 2 ≤ n * (y : ℤ) ^ 2 := by
        have hsq : 1 ≤ (y : ℤ) ^ 2 := by nlinarith
        calc
          2 ≤ n := hn
          _ = n * 1 := by ring
          _ ≤ n * (y : ℤ) ^ 2 := mul_le_mul_of_nonneg_left hsq (by omega)
      have hlarge : n * (y : ℤ) < |x| := by
        by_contra h
        have hle : |x| ≤ n * (y : ℤ) := le_of_not_gt h
        have hp := mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hny hx)
        nlinarith [hp]
      let y' : ℤ := (2 * n + 1) * (y : ℤ) - 2 * |x|
      let x' : ℤ := (2 * n + 1) * |x| - 2 * n * (n + 1) * (y : ℤ)
      have hy' : 0 < y' := by
        dsimp [y']
        by_contra h
        have hle : (2 * n + 1) * (y : ℤ) ≤ 2 * |x| := by omega
        have hsum : 0 ≤ 2 * |x| + (2 * n + 1) * (y : ℤ) := by
          positivity
        have hp := mul_nonneg (sub_nonneg.mpr hle) hsum
        nlinarith [hp, sq_nonneg (y : ℤ)]
      have hsmall : y' < (y : ℤ) := by dsimp [y']; nlinarith
      have hnew : x' ^ 2 - n * (n + 1) * y' ^ 2 = -1 := by
        calc
          x' ^ 2 - n * (n + 1) * y' ^ 2 =
              |x| ^ 2 - n * (n + 1) * (y : ℤ) ^ 2 := by dsimp [x', y']; ring
          _ = -1 := hnorm'
      have hcast : ((Int.toNat y' : ℕ) : ℤ) = y' := Int.toNat_of_nonneg hy'.le
      have hlt : Int.toNat y' < y := by
        exact_mod_cast (show ((Int.toNat y' : ℕ) : ℤ) < (y : ℤ) by rw [hcast]; exact hsmall)
      exact ih (Int.toNat y') hlt x' (by simpa only [hcast] using hnew)

/-- A Pell discriminant `n(n+1)` with `n ≥ 2` excludes the negative unit. -/
theorem norm_ne_neg_one (n x y : ℤ) (hn : 2 ≤ n) :
    x ^ 2 - n * (n + 1) * y ^ 2 ≠ -1 := by
  simpa only [Int.natCast_natAbs, sq_abs] using no_negative_nat_y n hn y.natAbs x

end DiophantineConsistency.ConsecutivePell

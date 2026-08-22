import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite borrow-block rigidity

This module isolates the elementary finite arithmetic behind a long binary borrow block.
After adding the all-ones lower word, the signed digit differences become nonnegative
coefficients.  If the resulting base-two evaluation is smaller than `2 ^ s`, every
coefficient in positions `s, ..., J - 1` must vanish.  For a ternary digit minus a binary
digit, vanishing of the shifted coefficient forces the digit pair `(0, 1)`.

The results are purely finite and make no analytic or conjectural assumptions.
-/

namespace LeanProofs.TwoBaseIntegerExponent.BorrowBlockCore

open Finset
open scoped BigOperators

/-- The nonnegative base-two expression obtained after adding the all-ones lower word. -/
def shiftedBinaryEvaluation (a : ℕ → ℕ) (J : ℕ) : ℕ :=
  1 + ∑ i ∈ range J, a i * 2 ^ i

/-- A shifted evaluation below `2 ^ s` has zero coefficients in positions
`s, ..., J - 1`. -/
theorem shiftedCoefficient_eq_zero_of_lt
    (a : ℕ → ℕ) (J s : ℕ)
    (hsmall : shiftedBinaryEvaluation a J < 2 ^ s)
    {i : ℕ} (hsi : s ≤ i) (hiJ : i < J) :
    a i = 0 := by
  by_contra hai
  have hai_one : 1 ≤ a i := Nat.one_le_iff_ne_zero.mpr hai
  have hpows : 2 ^ s ≤ 2 ^ i :=
    Nat.pow_le_pow_right (by omega) hsi
  have hterm : 2 ^ s ≤ a i * 2 ^ i := by
    calc
      2 ^ s ≤ 2 ^ i := hpows
      _ ≤ a i * 2 ^ i := by nlinarith
  have hsum : a i * 2 ^ i ≤ ∑ j ∈ range J, a j * 2 ^ j := by
    exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (a j * 2 ^ j))
      (Finset.mem_range.mpr hiJ)
  unfold shiftedBinaryEvaluation at hsmall
  omega

/-- The nonnegative shift of the difference between a ternary digit and a binary digit. -/
def borrowShift (ternaryDigit binaryDigit : ℕ → ℕ) (i : ℕ) : ℕ :=
  ternaryDigit i + 1 - binaryDigit i

/-- A shifted digit difference vanishes exactly at the borrow pair `(0, 1)`, provided the
binary entry is a bit. -/
theorem borrowShift_eq_zero_iff
    (ternaryDigit binaryDigit : ℕ → ℕ) {i : ℕ}
    (hbinary : binaryDigit i ≤ 1) :
    borrowShift ternaryDigit binaryDigit i = 0 ↔
      ternaryDigit i = 0 ∧ binaryDigit i = 1 := by
  simp only [borrowShift, Nat.sub_eq_zero_iff_le]
  omega

/-- The shifted evaluation of the differences between ternary digits and binary digits. -/
def digitBorrowEvaluation
    (ternaryDigit binaryDigit : ℕ → ℕ) (J : ℕ) : ℕ :=
  shiftedBinaryEvaluation (borrowShift ternaryDigit binaryDigit) J

/-- Small shifted evaluation forces every binary/ternary digit pair in the high block to be
the borrow pair `(0, 1)`. -/
theorem digitPair_eq_zero_one_of_evaluation_lt
    (ternaryDigit binaryDigit : ℕ → ℕ) (J s : ℕ)
    (hsmall : digitBorrowEvaluation ternaryDigit binaryDigit J < 2 ^ s)
    {i : ℕ} (hbinary : binaryDigit i ≤ 1) (hsi : s ≤ i) (hiJ : i < J) :
    ternaryDigit i = 0 ∧ binaryDigit i = 1 := by
  apply (borrowShift_eq_zero_iff ternaryDigit binaryDigit hbinary).mp
  apply shiftedCoefficient_eq_zero_of_lt (borrowShift ternaryDigit binaryDigit) J s
  · exact hsmall
  · exact hsi
  · exact hiJ

/-- A leading difference coefficient `2` contributes at least `2 ^ J + 1`, so its shifted
evaluation cannot lie below `2 ^ s` when `s ≤ J`. -/
theorem leadingTwoEvaluation_not_lt
    (J s tail : ℕ) (hsJ : s ≤ J) :
    ¬(2 ^ J + 1 + tail < 2 ^ s) := by
  intro hsmall
  have hpows : 2 ^ s ≤ 2 ^ J :=
    Nat.pow_le_pow_right (by omega) hsJ
  omega

end LeanProofs.TwoBaseIntegerExponent.BorrowBlockCore

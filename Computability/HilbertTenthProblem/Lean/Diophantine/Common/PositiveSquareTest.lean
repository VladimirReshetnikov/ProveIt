import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Basic

/-!
# Positive values of an integer square test

Putnam's construction multiplies a nonnegative candidate value by `1 - b²`.
Over the integers, a positive result forces the residual `b` to vanish.
This scalar fact is shared by the general function construction and the
prime-polynomial constructions, independently of their polynomial encodings.
-/

namespace Diophantine

/-- A positive integer square test has zero residual. The multiplier may
be zero a priori; strict positivity of the product rules that case out. -/
theorem eq_zero_of_mul_one_sub_sq_pos {a b : ℤ} (ha : 0 ≤ a)
    (hpos : 0 < a * (1 - b ^ 2)) : b = 0 := by
  have hb : b ^ 2 < 1 := sub_pos.mp (pos_of_mul_pos_right hpos ha)
  have hs : b ^ 2 = 0 :=
    le_antisymm (Int.le_of_lt_add_one hb) (sq_nonneg b)
  exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hs

/-- Complete positivity criterion for a nonnegative integer square test. -/
theorem mul_one_sub_sq_pos_iff {a b : ℤ} (ha : 0 ≤ a) :
    0 < a * (1 - b ^ 2) ↔ 0 < a ∧ b = 0 := by
  constructor
  · intro hpos
    have hb := eq_zero_of_mul_one_sub_sq_pos ha hpos
    exact ⟨by simpa [hb] using hpos, hb⟩
  · rintro ⟨hpos, rfl⟩
    simpa using hpos

end Diophantine

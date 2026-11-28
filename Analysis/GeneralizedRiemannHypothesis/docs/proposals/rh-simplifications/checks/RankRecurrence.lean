import Std

/-!
# The codimension recurrence and the cyclic example

The recurrence uses the standard library interfaces for linearly ordered
commutative rings. The final identity checks the rational expression for the
normalized deficit in the cyclic example.

Checked with Lean 4.32.0 and its bundled standard library:
    lean RankRecurrence.lean
-/

namespace RankRecurrence

open Lean.Grind

variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R]
  [Std.LawfulOrderLT R] [OrderedRing R]

/-- Iterate an affine upper bound with nonnegative slope. -/
theorem iterate (q : Nat → R) (p ν u : R) (hp : p ≤ 1) (h₀ : q 0 ≤ u)
    (step : ∀ j, q (j + 1) ≤ (1 - p) * q j + p * ν) (n : Nat) :
    q n ≤ ν + (1 - p) ^ n * (u - ν) := by
  have hslope : 0 ≤ 1 - p := by grind
  induction n with
  | zero =>
    simp only [Semiring.pow_zero, Semiring.one_mul]
    grind
  | succ n ih =>
    calc
      q (n + 1) ≤ (1 - p) * q n + p * ν := step n
      _ ≤ (1 - p) * (ν + (1 - p) ^ n * (u - ν)) + p * ν :=
        (OrderedAdd.add_le_left_iff _).mp (OrderedRing.mul_le_mul_of_nonneg_left ih hslope)
      _ = ν + (1 - p) ^ (n + 1) * (u - ν) := by
        rw [Semiring.pow_succ]
        grind

/-- Normalized codimension is at most one initially. -/
theorem normalized (q : Nat → R) (p ν : R) (hp : p ≤ 1) (h₀ : q 0 ≤ 1)
    (step : ∀ j, q (j + 1) ≤ (1 - p) * q j + p * ν) (n : Nat) :
    q n ≤ ν + (1 - p) ^ n * (1 - ν) :=
  iterate q p ν 1 hp h₀ step n

/-- Exact normalized deficit, written to expose its limiting constant. -/
theorem cyclic_deficit (x : Rat) (hx : 0 < x) :
    x * (19*x - 25) / (x * (x + 9)) = 19 - 196 / (x + 9) := by
  have hx₀ : x ≠ 0 := by grind
  have hx₉ : x + 9 ≠ 0 := by grind
  have hden : x * (x + 9) ≠ 0 := by grind
  grind

end RankRecurrence

#print axioms RankRecurrence.normalized
#print axioms RankRecurrence.cyclic_deficit

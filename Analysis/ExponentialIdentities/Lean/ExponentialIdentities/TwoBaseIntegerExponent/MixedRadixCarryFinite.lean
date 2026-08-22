import Mathlib

/-!
Finite arithmetic core of a mixed-radix floor-carry rectangle.

The dynamical density and inverse-limit statements used in the paper remain paper-level.
This module checks the four digit bounds and the local plaquette identity from Euclidean
division.  In particular, it makes no uniqueness claim at smooth rational endpoints.
-/

namespace LeanProofs.TwoBaseIntegerExponent.MixedRadixCarryFinite

/-- Horizontal digit on the lower edge of a mixed-radix square. -/
def lowerHorizontalDigit (a b z : ℕ) : ℕ := (z / b) % a

/-- Vertical digit on the left edge of a mixed-radix square. -/
def leftVerticalDigit (a b z : ℕ) : ℕ := (z / a) % b

/-- Horizontal digit on the upper edge of a mixed-radix square. -/
def upperHorizontalDigit (a z : ℕ) : ℕ := z % a

/-- Vertical digit on the right edge of a mixed-radix square. -/
def rightVerticalDigit (b z : ℕ) : ℕ := z % b

theorem lowerHorizontalDigit_lt {a b z : ℕ} (ha : 0 < a) :
    lowerHorizontalDigit a b z < a := Nat.mod_lt _ ha

theorem leftVerticalDigit_lt {a b z : ℕ} (hb : 0 < b) :
    leftVerticalDigit a b z < b := Nat.mod_lt _ hb

theorem upperHorizontalDigit_lt {a z : ℕ} (ha : 0 < a) :
    upperHorizontalDigit a z < a := Nat.mod_lt _ ha

theorem rightVerticalDigit_lt {b z : ℕ} (hb : 0 < b) :
    rightVerticalDigit b z < b := Nat.mod_lt _ hb

/-- Both directed carry totals are the remainder of `z` modulo `a * b`. -/
theorem mixedRadixPlaquette (a b z : ℕ) :
    b * lowerHorizontalDigit a b z + rightVerticalDigit b z =
      a * leftVerticalDigit a b z + upperHorizontalDigit a z := by
  simp only [lowerHorizontalDigit, rightVerticalDigit, leftVerticalDigit,
    upperHorizontalDigit]
  have hleft : b * ((z / b) % a) + z % b = z % (b * a) := by
    calc
      b * ((z / b) % a) + z % b =
          b * ((z % (b * a)) / b) + (z % (b * a)) % b := by
            rw [Nat.mod_mul_right_div_self]
            rw [Nat.mod_mod_of_dvd z (dvd_mul_right b a)]
      _ = z % (b * a) := Nat.div_add_mod _ _
  have hright : a * ((z / a) % b) + z % a = z % (a * b) := by
    calc
      a * ((z / a) % b) + z % a =
          a * ((z % (a * b)) / a) + (z % (a * b)) % a := by
            rw [Nat.mod_mul_right_div_self]
            rw [Nat.mod_mod_of_dvd z (dvd_mul_right a b)]
      _ = z % (a * b) := Nat.div_add_mod _ _
  rw [hleft, hright, Nat.mul_comm]

end LeanProofs.TwoBaseIntegerExponent.MixedRadixCarryFinite

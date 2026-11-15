import Std

/-!
The four-point group table for y^2 = x^3 - x.

This file verifies ONLY the finite table and its two-generator description.
It does not prove that these are all rational points, and it does not prove
that the chord-and-tangent law induces this table. Those arithmetic bridges
are separate obligations described in LeanPlan.md and the paper.
-/

namespace MordellWeilIPRA.E1FiniteTable

inductive Point where
  | origin
  | minusOne
  | zero
  | plusOne
  deriving Repr, DecidableEq

open Point

def add : Point → Point → Point
  | origin, y => y
  | x, origin => x
  | minusOne, minusOne => origin
  | zero, zero => origin
  | plusOne, plusOne => origin
  | minusOne, zero => plusOne
  | zero, minusOne => plusOne
  | minusOne, plusOne => zero
  | plusOne, minusOne => zero
  | zero, plusOne => minusOne
  | plusOne, zero => minusOne

theorem add_assoc (x y z : Point) : add (add x y) z = add x (add y z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem add_comm (x y : Point) : add x y = add y x := by
  cases x <;> cases y <;> rfl

theorem add_origin (x : Point) : add x origin = x := by
  cases x <;> rfl

theorem add_self (x : Point) : add x x = origin := by
  cases x <;> rfl

def coefficients : Point → Bool × Bool
  | origin => (false, false)
  | minusOne => (true, false)
  | zero => (false, true)
  | plusOne => (true, true)

def bitMultiple (b : Bool) (x : Point) : Point :=
  if b then x else origin

theorem two_generators (x : Point) :
    add (bitMultiple (coefficients x).1 minusOne)
      (bitMultiple (coefficients x).2 zero) = x := by
  cases x <;> rfl

theorem coefficients_injective (x y : Point)
    (h : coefficients x = coefficients y) : x = y := by
  cases x <;> cases y <;> simp_all [coefficients]

end MordellWeilIPRA.E1FiniteTable

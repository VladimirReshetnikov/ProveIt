import Surreal.Foundations.SignSequenceCutOperation
import Mathlib.Order.GameAdd

/-!
# Checked recursion relations for canonical signs

For `found:sub:recursionmeasure`, Mathlib's game-addition relation on pairs
provides a checked well-founded relation that decreases when either argument
is replaced by an option. This is the source's relation-based termination
route; it does not identify the rank with a Hessenberg natural sum.

Numerical order is not well founded. Maximum birthday and ordinary ordinal
addition also fail as proposed strictly decreasing measures, as witnessed
by explicit canonical signs below.
-/

universe u

namespace Surreal.Foundations.SignSequence

/-- Every canonical left option is a proper sign prefix. -/
theorem leftOption_simpler (x : SignSequence.{u}) (i : LeftIndex x) :
    Simpler (leftOption x i) x := truncate_simpler x _ i.val.property

/-- Every canonical right option is a proper sign prefix. -/
theorem rightOption_simpler (x : SignSequence.{u}) (i : RightIndex x) :
    Simpler (rightOption x i) x := truncate_simpler x _ i.val.property

/-- Exactly one coordinate becomes simpler while the other is fixed. -/
abbrev PairSimpler : (SignSequence.{u} × SignSequence.{u}) →
    (SignSequence.{u} × SignSequence.{u}) → Prop := Prod.GameAdd Simpler Simpler

/-- A native well-founded relation for binary recursive definitions. -/
theorem pairSimpler_wellFounded : WellFounded (PairSimpler :
    (SignSequence.{u} × SignSequence.{u}) → _ → Prop) :=
  simpler_wellFounded.prod_gameAdd simpler_wellFounded

theorem pairSimpler_leftOption_left (x y : SignSequence.{u}) (i : LeftIndex x) :
    PairSimpler (leftOption x i, y) (x, y) := .fst (leftOption_simpler x i)

theorem pairSimpler_rightOption_left (x y : SignSequence.{u}) (i : RightIndex x) :
    PairSimpler (rightOption x i, y) (x, y) := .fst (rightOption_simpler x i)

theorem pairSimpler_leftOption_right (x y : SignSequence.{u}) (i : LeftIndex y) :
    PairSimpler (x, leftOption y i) (x, y) := .snd (leftOption_simpler y i)

theorem pairSimpler_rightOption_right (x y : SignSequence.{u}) (i : RightIndex y) :
    PairSimpler (x, rightOption y i) (x, y) := .snd (rightOption_simpler y i)

/-- The negative finite ordinal signs form the explicit descending chain
from `found:sub:recursionmeasure`. -/
theorem negative_finite_ordinals_strictAnti :
    StrictAnti (fun n : ℕ => -ofOrdinal (n : Ordinal.{u})) := by
  intro m n hmn
  apply (neg_lt_neg_iff _ _).mpr
  apply ofOrdinal_strictMono
  exact_mod_cast hmn

/-- Numerical order cannot be used as a well-founded recursion relation. -/
theorem numerical_not_wellFounded :
    ¬ WellFounded ((· < ·) : SignSequence.{u} → SignSequence.{u} → Prop) := by
  intro h
  obtain ⟨_, ⟨n, rfl⟩, hmin⟩ := h.has_min
    (Set.range (fun n : ℕ => -ofOrdinal (n : Ordinal.{u}))) ⟨-ofOrdinal 0, 0, rfl⟩
  exact hmin _ ⟨n + 1, rfl⟩ (negative_finite_ordinals_strictAnti (Nat.lt_succ_self n))

/-- Decreasing the smaller birthday need not decrease the maximum. -/
theorem maximum_birthday_not_decreasing :
    ∃ x' x y : SignSequence.{u}, Simpler x' x ∧
      max x'.birthday y.birthday = max x.birthday y.birthday := by
  refine ⟨0, ofOrdinal 1, ofOrdinal 2, ?_, ?_⟩
  · exact ⟨⟨by simp, by simp⟩, by simp⟩
  · have h02 : (0 : Ordinal.{u}) ≤ 2 := by exact_mod_cast (by decide : (0 : ℕ) ≤ 2)
    have h12 : (1 : Ordinal.{u}) ≤ 2 := by exact_mod_cast (by decide : (1 : ℕ) ≤ 2)
    simp only [birthday_zero, birthday_ofOrdinal, max_eq_right h02, max_eq_right h12]

/-- Ordinary ordinal addition can absorb a strict decrease of its left
argument; this is a different obstruction from the maximum counterexample. -/
theorem ordinal_sum_birthday_not_decreasing :
    ∃ x' x y : SignSequence.{u}, Simpler x' x ∧
      x'.birthday + y.birthday = x.birthday + y.birthday := by
  refine ⟨0, ofOrdinal 1, ofOrdinal Ordinal.omega0, ?_, ?_⟩
  · exact ⟨⟨by simp, by simp⟩, by simp⟩
  · simp only [birthday_zero, birthday_ofOrdinal, zero_add, Ordinal.one_add_omega0]

end Surreal.Foundations.SignSequence

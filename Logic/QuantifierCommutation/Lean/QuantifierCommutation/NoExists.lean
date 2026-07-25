import QuantifierCommutation.Counterexample

/-!
# Nested nonexistence quantifiers do not commute

Here `NoExists P` is exactly `¬ ∃ x, P x`.  Consequently, nesting the
operation alternates polarity:

`NoExists (fun x => NoExists (fun y => R x y))`

unfolds to `¬ ∃ x, ¬ ∃ y, R x y`; it is not the same as jointly denying
the existence of a pair.  A two-element countermodel distinguishes this
formula from the one obtained by swapping `x` and `y`.
-/

namespace LeanProofs
namespace QuantifierCommutation

/-- The precise meaning assigned here to the quantifier written `∄`. -/
def NoExists {α : Sort u} (P : α → Prop) : Prop :=
  ¬ ∃ x, P x

/-- First bind `x` with `∄`, then bind `y` with `∄`. -/
def NoExistsXY {α : Sort u} {β : Sort v} (R : α → β → Prop) : Prop :=
  NoExists fun x => NoExists fun y => R x y

/-- The same two `∄` binders in the opposite order. -/
def NoExistsYX {α : Sort u} {β : Sort v} (R : α → β → Prop) : Prop :=
  NoExists fun y => NoExists fun x => R x y

theorem noExistsXY_unfold {α : Sort u} {β : Sort v}
    (R : α → β → Prop) :
    NoExistsXY R ↔ ¬ ∃ x, ¬ ∃ y, R x y :=
  Iff.rfl

theorem noExistsYX_unfold {α : Sort u} {β : Sort v}
    (R : α → β → Prop) :
    NoExistsYX R ↔ ¬ ∃ y, ¬ ∃ x, R x y :=
  Iff.rfl

/-- A two-element type for the noncommutation countermodel. -/
inductive Two : Type
  | first
  | second

/-- Every row contains `first`, while the `second` column is empty. -/
def firstColumn (_x : Two) (y : Two) : Prop :=
  y = .first

/-- `∄ x, ∄ y, firstColumn x y` holds. -/
theorem firstColumn_noExistsXY : NoExistsXY firstColumn := by
  rintro ⟨x, noY⟩
  exact noY ⟨.first, rfl⟩

/-- `∄ y, ∄ x, firstColumn x y` does not hold: its outer existential
counterwitness is the empty `second` column. -/
theorem firstColumn_not_noExistsYX : ¬ NoExistsYX firstColumn := by
  intro h
  apply h
  refine ⟨.second, ?_⟩
  rintro ⟨x, hSecond⟩
  cases hSecond

/-- A concrete same-type relation for which the two nesting orders have
opposite truth values. -/
theorem noExists_counterexample :
    NoExistsXY firstColumn ∧ ¬ NoExistsYX firstColumn :=
  ⟨firstColumn_noExistsXY, firstColumn_not_noExistsYX⟩

/-- Thus even the forward implication needed to swap the two `∄` binders
fails. -/
theorem noExists_swap_implication_fails :
    ¬ (NoExistsXY firstColumn → NoExistsYX firstColumn) :=
  implication_fails firstColumn_noExistsXY firstColumn_not_noExistsYX

/-- Therefore two adjacent `∄` quantifiers cannot in general be swapped. -/
theorem noExists_not_commutative :
    ¬ (NoExistsXY firstColumn ↔ NoExistsYX firstColumn) :=
  not_equivalent firstColumn_noExistsXY firstColumn_not_noExistsYX

end QuantifierCommutation
end LeanProofs

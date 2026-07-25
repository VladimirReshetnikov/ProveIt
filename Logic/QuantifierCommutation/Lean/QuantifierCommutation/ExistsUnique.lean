import QuantifierCommutation.Counterexample

/-!
# Nested unique-existence quantifiers do not commute

The three-by-three relation below has exactly one row containing exactly one
related element, but all three columns contain exactly one related element.
Thus `∃! x, ∃! y, R x y` is true and its binder-swapped counterpart is false.
-/

namespace LeanProofs
namespace QuantifierCommutation

/-- Canonical unique-existence semantics: there is a witness satisfying `P`,
and every satisfying element is equal to that witness.  This is the
dependency-free definition denoted by `∃! x, P x` in Lean's mathematics
library. -/
def ExistsUnique {α : Sort u} (P : α → Prop) : Prop :=
  ∃ x, P x ∧ ∀ y, P y → y = x

/-- First bind `x` with unique existence, then bind `y`. -/
def ExistsUniqueXY {α : Sort u} {β : Sort v}
    (R : α → β → Prop) : Prop :=
  ExistsUnique fun x => ExistsUnique fun y => R x y

/-- The same unique-existence binders in the opposite order. -/
def ExistsUniqueYX {α : Sort u} {β : Sort v}
    (R : α → β → Prop) : Prop :=
  ExistsUnique fun y => ExistsUnique fun x => R x y

theorem existsUniqueXY_unfold {α : Sort u} {β : Sort v}
    (R : α → β → Prop) :
    ExistsUniqueXY R ↔
      ∃ x, (∃ y, R x y ∧ ∀ y', R x y' → y' = y) ∧
        ∀ x', (∃ y, R x' y ∧ ∀ y', R x' y' → y' = y) → x' = x :=
  Iff.rfl

theorem existsUniqueYX_unfold {α : Sort u} {β : Sort v}
    (R : α → β → Prop) :
    ExistsUniqueYX R ↔
      ∃ y, (∃ x, R x y ∧ ∀ x', R x' y → x' = x) ∧
        ∀ y', (∃ x, R x y' ∧ ∀ x', R x' y' → x' = x) → y' = y :=
  Iff.rfl

/-- A three-element type for the unique-existence countermodel. -/
inductive Three : Type
  | a
  | b
  | c

/-- The relation consists of the three pairs `(a,a)`, `(b,b)`, and `(b,c)`.
Its row degrees are `1, 2, 0`, while its column degrees are `1, 1, 1`. -/
inductive uniqueRelation : Three → Three → Prop
  | aa : uniqueRelation .a .a
  | bb : uniqueRelation .b .b
  | bc : uniqueRelation .b .c

/-- Any witness together with a per-point uniqueness check yields unique
existence over `Three`. -/
theorem three_existsUnique_intro {P : Three → Prop} {w : Three}
    (hw : P w)
    (ha : P .a → Three.a = w)
    (hb : P .b → Three.b = w)
    (hc : P .c → Three.c = w) :
    ExistsUnique P := by
  refine ⟨w, hw, ?_⟩
  intro t ht
  cases t with
  | a => exact ha ht
  | b => exact hb ht
  | c => exact hc ht

theorem rowA_unique : ExistsUnique fun y => uniqueRelation .a y :=
  three_existsUnique_intro .aa (fun _ => rfl)
    (fun h => nomatch h) (fun h => nomatch h)

theorem columnA_unique : ExistsUnique fun x => uniqueRelation x .a :=
  three_existsUnique_intro .aa (fun _ => rfl)
    (fun h => nomatch h) (fun h => nomatch h)

theorem columnB_unique : ExistsUnique fun x => uniqueRelation x .b :=
  three_existsUnique_intro .bb (fun h => nomatch h)
    (fun _ => rfl) (fun h => nomatch h)

theorem columnC_unique : ExistsUnique fun x => uniqueRelation x .c :=
  three_existsUnique_intro .bc (fun h => nomatch h)
    (fun _ => rfl) (fun h => nomatch h)

/-- Only row `a` has a unique related element. -/
theorem uniqueRelation_existsUniqueXY : ExistsUniqueXY uniqueRelation := by
  refine ⟨.a, rowA_unique, ?_⟩
  intro x hx
  cases x with
  | a => rfl
  | b =>
      rcases hx with ⟨y, _hy, hUnique⟩
      have hb : Three.b = y := hUnique .b .bb
      have hc : Three.c = y := hUnique .c .bc
      have : Three.b = Three.c := hb.trans hc.symm
      cases this
  | c =>
      rcases hx with ⟨y, hy, _hUnique⟩
      cases hy

/-- The reverse nesting is not uniquely inhabited, since both columns `a`
and `b` (indeed, all three columns) have unique predecessors. -/
theorem uniqueRelation_not_existsUniqueYX :
    ¬ ExistsUniqueYX uniqueRelation := by
  rintro ⟨y, _hy, hUnique⟩
  have ha : Three.a = y := hUnique .a columnA_unique
  have hb : Three.b = y := hUnique .b columnB_unique
  have : Three.a = Three.b := ha.trans hb.symm
  cases this

/-- A concrete same-type relation for which the two unique-existence nesting
orders have opposite truth values. -/
theorem existsUnique_counterexample :
    ExistsUniqueXY uniqueRelation ∧ ¬ ExistsUniqueYX uniqueRelation :=
  ⟨uniqueRelation_existsUniqueXY, uniqueRelation_not_existsUniqueYX⟩

/-- Thus even the forward implication needed to swap the two `∃!` binders
fails. -/
theorem existsUnique_swap_implication_fails :
    ¬ (ExistsUniqueXY uniqueRelation → ExistsUniqueYX uniqueRelation) :=
  implication_fails uniqueRelation_existsUniqueXY
    uniqueRelation_not_existsUniqueYX

/-- Therefore two adjacent `∃!` quantifiers cannot in general be swapped. -/
theorem existsUnique_not_commutative :
    ¬ (ExistsUniqueXY uniqueRelation ↔ ExistsUniqueYX uniqueRelation) :=
  not_equivalent uniqueRelation_existsUniqueXY
    uniqueRelation_not_existsUniqueYX

end QuantifierCommutation
end LeanProofs

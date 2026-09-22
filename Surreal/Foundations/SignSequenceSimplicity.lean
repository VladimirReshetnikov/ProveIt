import Surreal.Foundations.SignSequenceOptions
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.WellFounded

/-!
# Simplest elements of convex sets of sign sequences

Any nonempty order-convex set of sign sequences has a unique element of
minimum birthday. This element is a sign prefix of every element of the
set. In particular, once a separated cut has any separator, it has a
unique simplest separator. Existence of a separator for arbitrary small
cuts is established independently of this simplicity argument.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- A minimum-birthday element of an order-convex set is a sign prefix of
every element of that set. Canonical options would otherwise supply a
shorter element between two members. -/
theorem isPrefix_of_minimum_birthday {s : Set SignSequence.{u}}
    (hs : s.OrdConnected) {x : SignSequence.{u}} (hx : x ∈ s)
    (hmin : ∀ y ∈ s, x.birthday ≤ y.birthday) {y : SignSequence.{u}} (hy : y ∈ s) :
    IsPrefix x y := by
  apply isPrefix_of_separates_options x y
  · intro i
    by_contra! hle
    have hm : leftOption x i ∈ s := hs.out hy hx ⟨hle, (leftOption_lt x i).le⟩
    exact (not_le_of_gt i.val.property) (hmin _ hm)
  · intro i
    by_contra! hle
    have hm : rightOption x i ∈ s := hs.out hx hy ⟨(lt_rightOption x i).le, hle⟩
    exact (not_le_of_gt i.val.property) (hmin _ hm)

/-- Every nonempty order-convex set has a unique element which is a sign
prefix of all its members. The minimum birthday is selected using ordinal
well-foundedness, not completeness of the numerical order. -/
theorem existsUnique_prefix_of_ordConnected {s : Set SignSequence.{u}}
    (hs : s.OrdConnected) (hne : s.Nonempty) :
    ∃! x, x ∈ s ∧ ∀ y ∈ s, IsPrefix x y := by
  obtain ⟨x, hx, hmin⟩ := (InvImage.wf birthday Ordinal.lt_wf).has_min s hne
  have hp : ∀ y ∈ s, IsPrefix x y :=
    fun y hy => isPrefix_of_minimum_birthday hs hx (fun z hz => le_of_not_gt (hmin z hz)) hy
  refine ⟨x, ⟨hx, hp⟩, ?_⟩
  intro y hy
  exact IsPrefix.antisymm (hy.2 x hx) (hp y hy.1)

/-- The birthday formulation of the simplest-element theorem. -/
theorem existsUnique_minimum_birthday_of_ordConnected {s : Set SignSequence.{u}}
    (hs : s.OrdConnected) (hne : s.Nonempty) :
    ∃! x, x ∈ s ∧ ∀ y ∈ s, x.birthday ≤ y.birthday := by
  obtain ⟨x, hx, _⟩ := existsUnique_prefix_of_ordConnected hs hne
  refine ⟨x, ⟨hx.1, fun y hy => (hx.2 y hy).1⟩, ?_⟩
  intro y hy
  exact IsPrefix.antisymm
    (isPrefix_of_minimum_birthday hs hy.1 hy.2 hx.1) (hx.2 y hy.1)

/-- The separators of any cut form an order-convex subset of the sign
carrier; the cut need not yet be known to have a separator. -/
theorem ordConnected_separators
    (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    Set.OrdConnected {x | c.IsRealizedBy x} := by
  constructor
  intro x hx y hy z hz
  exact ⟨fun i => (hx.1 i).trans_le hz.1, fun i => hz.2.trans_lt (hy.2 i)⟩

/-- Given existence, the simplest cut separator is unique and is a sign
prefix of every separator. No small-cut filling hypothesis is used here. -/
theorem existsUnique_simplest_separator
    (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·))
    (hc : ∃ x, c.IsRealizedBy x) :
    ∃! x, c.IsRealizedBy x ∧ ∀ y, c.IsRealizedBy y → IsPrefix x y :=
  existsUnique_prefix_of_ordConnected (ordConnected_separators c) hc

end

end Surreal.Foundations.SignSequence

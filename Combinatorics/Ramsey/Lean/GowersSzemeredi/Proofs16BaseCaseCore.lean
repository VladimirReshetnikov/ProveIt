import GowersSzemeredi.Proofs16BoxGeometry

/-!
# The proper-box repair for Gowers's Section 16

This module records the structural repair used by the shared catalogue and
the one-dimensional base case.  A box is required to
be genuine axis by axis, and the loss parameter in multiple linearity is
restricted to `(0,1]`.  The compact witness at the end exposes the loophole in
the old predicate: a step-zero progression can have singleton carrier and an
arbitrarily inflated formal width.

The shared Section 16 catalogue now uses these conditions. The former
proper-predicate names remain as reducible compatibility aliases.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- Compatibility name for the migrated shared predicate. -/
abbrev ProperMultiplyLinear {N k : Nat} [NeZero N] (gamma r : Real)
    (Gamma : Finset (Point N k × ZMod N)) : Prop :=
  MultiplyLinear gamma r Gamma

/-- Compatibility name for the migrated fixed-dimensional assertion. -/
abbrev ProperTheorem162At (k : Nat) : Prop := Theorem162At k

/-! ## The improper-box loophole -/

/-- A step-zero one-dimensional box.  Its carrier is a singleton for every
positive formal length. -/
private def inflatedSingletonBox {N : Nat} (x : Point N 1) (L : Nat) : Box N 1 where
  axis := fun _ => { start := x 0, step := 0, length := L }
  commonDiff := 0
  axis_step := by intro i; rfl

@[simp] private lemma inflatedSingletonBox_width {N : Nat}
    (x : Point N 1) (L : Nat) : (inflatedSingletonBox x L).width = L := by
  simp [inflatedSingletonBox, Box.width]

@[simp] private lemma inflatedSingletonBox_carrier {N : Nat} [NeZero N]
    (x : Point N 1) (L : Nat) (hL : 0 < L) :
    (inflatedSingletonBox x L).carrier = {x} := by
  classical
  ext y
  simp only [Box.carrier, inflatedSingletonBox, Finset.mem_filter,
    Finset.mem_univ, true_and, ModAP.carrier, Finset.mem_image,
    Finset.mem_singleton]
  constructor
  · intro hy
    apply funext
    intro i
    fin_cases i
    obtain ⟨j, hj⟩ := hy 0
    simpa using hj.symm
  · rintro rfl i
    fin_cases i
    refine ⟨⟨0, hL⟩, ?_⟩
    simp

/-- A singleton carrier can have arbitrarily large formal width, but the
representing box is necessarily improper. -/
theorem exists_improper_singleton_box_of_width {N L : Nat} [NeZero N]
    (x : Point N 1) (hL : 2 ≤ L) :
    ∃ P : Box N 1, P.carrier = {x} ∧ P.width = L ∧ ¬ P.IsProper := by
  classical
  refine ⟨inflatedSingletonBox x L,
    inflatedSingletonBox_carrier x L (by omega),
    inflatedSingletonBox_width x L, ?_⟩
  intro hproper
  have haxis := hproper 0
  rw [ModAP.IsProper] at haxis
  have hcarrier : ((inflatedSingletonBox x L).axis 0).carrier = {x 0} := by
    ext z
    simp only [inflatedSingletonBox, ModAP.carrier, Finset.mem_image,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      simp
    · rintro rfl
      exact ⟨⟨0, by omega⟩, by simp⟩
  rw [hcarrier] at haxis
  have hLone : 1 = L := by simpa [inflatedSingletonBox] using haxis
  omega

end LeanProofs.GowersSzemeredi

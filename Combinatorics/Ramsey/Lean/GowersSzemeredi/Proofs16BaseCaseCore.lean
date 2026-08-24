import GowersSzemeredi.Section16

/-!
# The proper-box repair for Gowers's Section 16

This small isolated module records the structural repair needed before the
base case can be folded into the statement catalogue.  A box is required to
be genuine axis by axis, and the loss parameter in multiple linearity is
restricted to `(0,1]`.  The compact witness at the end exposes the loophole in
the old predicate: a step-zero progression can have singleton carrier and an
arbitrarily inflated formal width.

Nothing here changes the shared Section 16 statement catalogue.  The
temporary names are intended to disappear once that catalogue is migrated.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

namespace Box

/-- A box is genuine when each modular arithmetic-progression axis is
proper. -/
def IsProper {N k : Nat} (P : Box N k) : Prop :=
  ∀ i, (P.axis i).IsProper

end Box

/-- Temporary repaired form of `MultiplyLinear`. -/
def ProperMultiplyLinear {N k : Nat} [NeZero N] (gamma r : Real)
    (Gamma : Finset (Point N k × ZMod N)) : Prop :=
  ∀ eta : Real, 0 < eta → eta ≤ 1 → ∀ P : Box N k, P.IsProper →
    ∃ M q : Nat, ∃ H : Finset (Point N k),
      ∃ Q : Fin M → Box N k,
        ∃ mu : Fin M → Fin q → Point N k → ZMod N,
          H ⊆ P.carrier ∧ (1 - eta) * P.carrier.card ≤ H.card ∧
          IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
          (q : Real) ≤ (multipleQ (r⁻¹ * eta) gamma k) ^ r ∧
          (∀ j, (P.width : Real) ^
              ((multipleC (r⁻¹ * eta) gamma k) ^ r) ≤ (Q j).width) ∧
          (∀ j i, IsMultilinear (mu j i)) ∧
          ∀ j x, x ∈ (Q j).carrier → x ∈ H → ∀ y,
            (x, y) ∈ Gamma → ∃ i, y = mu j i x

/-- Temporary repaired fixed-dimensional assertion of Theorem 16.2. -/
def ProperTheorem162At (k : Nat) : Prop :=
  ∀ gamma theta : Real, 0 < gamma → gamma ≤ 1 →
    0 < theta → theta ≤ 1 → ∃ N0 : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
        ∀ Gamma : Finset (Point N k × ZMod N),
          (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ k →
          RelationProductProperty gamma Gamma →
          ∃ J : Finset (Point N k),
            (1 - theta) * (N : Real) ^ k ≤ J.card ∧
            ProperMultiplyLinear gamma
              (gamma ^ (-(2 : Int)) * multipleS theta gamma k)
              (restrictRelation Gamma J)

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

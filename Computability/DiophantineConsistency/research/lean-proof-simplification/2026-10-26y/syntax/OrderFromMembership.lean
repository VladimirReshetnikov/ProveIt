import Mathlib.Order.RelClasses

/-! Reconstruct the internal order from its three strict-order facts.
The order of the disjuncts in `≤` changes. The explicit bridge below is part
of the proposal: the production `LeRel` definition stays unchanged. -/
namespace ProofSimplification
universe u

noncomputable abbrev orderFromMembership {V : Type u} (P : V → Prop)
    (r : V → V → Prop)
    (hirr : ∀ x, P x → ¬ r x x)
    (htrans : ∀ x y z, P z → r y z → r x y → r x z)
    (htri : ∀ x y, P x → P y → r x y ∨ x = y ∨ r y x) :
    LinearOrder {x : V // P x} := by
  classical
  let s : {x : V // P x} → {x : V // P x} → Prop := fun x y => r x.val y.val
  letI : IsStrictTotalOrder {x : V // P x} s := {
    irrefl := fun x => hirr x.val x.property
    trans := fun x y z hxy hyz => htrans x.val y.val z.val z.property hyz hxy
    trichotomous := fun x y hxy hyx =>
      Subtype.ext (((htri x.val y.val x.property y.property).resolve_left hxy).resolve_right hyx)
  }
  exact linearOrderOfSTO s

section Contract
variable {V : Type u} (P : V → Prop) (r : V → V → Prop)
    (hirr : ∀ x, P x → ¬ r x x)
    (htrans : ∀ x y z, P z → r y z → r x y → r x z)
    (htri : ∀ x y, P x → P y → r x y ∨ x = y ∨ r y x)
    (x y : {x : V // P x})

/-- The original mathematical nonstrict relation is preserved. -/
theorem le_iff_old :
    @LE.le _ (orderFromMembership P r hirr htrans htri).toLE x y ↔
      r x.val y.val ∨ x.val = y.val := by
  change (x = y ∨ r x.val y.val) ↔ r x.val y.val ∨ x.val = y.val
  simp only [Subtype.ext_iff, or_comm]

/-- Strict membership remains definitionally equal. -/
example : @LT.lt _ (orderFromMembership P r hirr htrans htri).toLT x y = r x.val y.val := rfl

/-- This is the precise new definitional shape of nonstrict order. -/
example : @LE.le _ (orderFromMembership P r hirr htrans htri).toLE x y =
    (x = y ∨ r x.val y.val) := rfl
end Contract

#print axioms orderFromMembership
#print axioms le_iff_old
end ProofSimplification

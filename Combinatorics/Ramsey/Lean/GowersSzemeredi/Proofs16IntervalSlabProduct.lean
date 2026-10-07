import GowersSzemeredi.Proofs16SlabProductProperty
import GowersSzemeredi.Proofs16CoordinateFaces

/-! Short interval slabs supply genuine unit-product examples for arbitrary
bounded-alphabet words. The explicit sufficient support budget is 4*L*R<=N. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace LeanProofs.GowersSzemeredi

theorem section16_modInterval_sumset_card_le {N : Nat} (L : Nat) :
    ((modInterval N 0 L).carrier + (modInterval N 0 L).carrier).card ≤ 2 * L := by
  classical
  have hsub : (modInterval N 0 L).carrier + (modInterval N 0 L).carrier ⊆
      (modInterval N 0 (2 * L)).carrier := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨⟨(i : Nat) + j, by have := i.isLt; have := j.isLt; dsimp [modInterval] at *; omega⟩,
      Finset.mem_univ _, ?_⟩
    simp [modInterval, Nat.cast_add]
  apply (Finset.card_le_card hsub).trans
  change (Finset.univ.image (fun i : Fin (2 * L) => (0 : ZMod N) + (i : Nat) * 1)).card ≤ 2 * L
  calc
    _ ≤ (Finset.univ : Finset (Fin (2 * L))).card := Finset.card_image_le
    _ = 2 * L := by simp

/-- The word can be arbitrary subject to its alphabet on the slab domain.
This verifies the actual weighted product property, not a substitute cover
or a restriction to unweighted energies. -/
theorem section16_interval_slab_unit_product {N k L R : Nat} [NeZero N]
    (f : ZMod N → ZMod N)
    (hf : ∀ x ∈ (modInterval N 0 L).carrier, f x ∈ (modInterval N 0 R).carrier)
    (hsize : 4 * L * R ≤ N) :
    HasProductProperty (lastProductSet (Finset.univ : Finset (Point N k)) (modInterval N 0 L).carrier)
      (fun z => f (section16Last z)) 1 := by
  apply section16_slab_unit_product _ _ f hf
  exact (Nat.mul_le_mul (section16_modInterval_sumset_card_le L)
    (section16_modInterval_sumset_card_le R)).trans (by nlinarith only [hsize])

/-- The same examples satisfy the relation-level product property used by
the structural extraction, because every contained partial graph inherits
it from this graph. -/
theorem section16_interval_slab_relation_product {N k L R : Nat} [NeZero N]
    (f : ZMod N → ZMod N)
    (hf : ∀ x ∈ (modInterval N 0 L).carrier, f x ∈ (modInterval N 0 R).carrier)
    (hsize : 4 * L * R ≤ N) :
    RelationProductProperty 1
      (partialGraph (lastProductSet (Finset.univ : Finset (Point N k)) (modInterval N 0 L).carrier)
        (fun z => f (section16Last z))) :=
  partialGraph_relationProductProperty (section16_interval_slab_unit_product f hf hsize)

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs16FixedColumnWordFamilies
import GowersSzemeredi.Proofs16RelationWordImages

/-! Compatible arbitrary-relation words in the common fixed-length word
space. The transport preserves both word counts and endpoint identities. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def fixedRelationWordRepresentations {N k : Nat} [NeZero N] (B : Finset (ZMod N))
    (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop) (a : ColumnAnchorTuple N k) :
    Finset (ColumnWord N (k+1)) :=
  (relationWordRepresentations B R (columnAnchorList a)).map
    (columnWordLengthEquiv (columnAnchorList_length a)).toEmbedding

theorem fixedRelationWordRepresentations_card {N k : Nat} [NeZero N]
    (B : Finset (ZMod N)) (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    (a : ColumnAnchorTuple N k) :
    (fixedRelationWordRepresentations B R a).card =
      (relationWordRepresentations B R (columnAnchorList a)).card := Finset.card_map _

/-- Fixed-length transport preserves the original entries, alternating
value, and every endpoint identity of the same representation. -/
theorem fixedRelationWordRepresentations_spec {N k : Nat} [NeZero N]
    (B : Finset (ZMod N)) (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (a : ColumnAnchorTuple N k)
    (hident : ∀ v ∈ relationWordRepresentations B R (columnAnchorList a),
      ColumnWordIdentity T L r (columnAnchorList a) v)
    {w : ColumnWord N (k+1)} (hw : w ∈ fixedRelationWordRepresentations B R a) :
    (∀ x ∈ columnWordEntries w, x ∈ B) ∧
      columnWordValue w = columnAnchorEval id (columnAnchorList a) ∧
      ColumnListIdentity T L r (columnAnchorList a) (columnWordEntries w) := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
  have hs := relationWordRepresentations_spec B R (columnAnchorList a) v hv
  change (∀ x ∈ columnWordEntries (columnWordLengthEquiv _ v), x ∈ B) ∧
    columnWordValue (columnWordLengthEquiv _ v) = _ ∧
    ColumnListIdentity T L r _ (columnWordEntries (columnWordLengthEquiv _ v))
  rw [columnWordLengthEquiv_entries]
  refine ⟨columnWordEntries_mem B v hs.1, ?_, (hident v hv).to_list⟩
  exact (columnWordLengthEquiv_eval _ id v).trans hs.2

end LeanProofs.GowersSzemeredi

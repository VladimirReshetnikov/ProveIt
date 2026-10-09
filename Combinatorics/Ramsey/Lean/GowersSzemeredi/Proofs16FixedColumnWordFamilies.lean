import GowersSzemeredi.Proofs16ColumnModelPacking

/-! Put representations of equally long anchor lists in one common word type. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

abbrev ColumnAnchorTuple (N k : Nat) := ZMod N × (Fin k → ZMod N)

def columnAnchorList {N k : Nat} (a : ColumnAnchorTuple N k) : List (ZMod N) :=
  a.1 :: List.ofFn a.2

theorem columnAnchorList_length {N k : Nat} (a : ColumnAnchorTuple N k) :
    (columnAnchorList a).length = k+1 := by simp [columnAnchorList]

def columnWordLengthEquiv {N j k : Nat} (h : j = k) : ColumnWord N j ≃ ColumnWord N k :=
  Equiv.cast (congrArg (ColumnWord N) h)

theorem columnWordLengthEquiv_eval {N j k : Nat} (h : j = k)
    (f : ZMod N → ZMod N) (w : ColumnWord N j) :
    columnWordEval f (columnWordLengthEquiv h w) = columnWordEval f w := by
  subst k; rfl

theorem columnWordLengthEquiv_entries {N j k : Nat} (h : j = k) (w : ColumnWord N j) :
    columnWordEntries (columnWordLengthEquiv h w) = columnWordEntries w := by
  subst k; rfl

def fixedColumnWordRepresentations {N k : Nat} [NeZero N] (B : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (a : ColumnAnchorTuple N k) : Finset (ColumnWord N (k+1)) :=
  (columnWordRepresentations B T L r (columnAnchorList a)).map
    (columnWordLengthEquiv (columnAnchorList_length a)).toEmbedding

theorem fixedColumnWordRepresentations_card {N k : Nat} [NeZero N] (B : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (a : ColumnAnchorTuple N k) :
    (fixedColumnWordRepresentations B T L r a).card =
      (columnWordRepresentations B T L r (columnAnchorList a)).card := Finset.card_map _

/-- Transport preserves entries, represented values, and every already
proved identity; the finite families retain their exact cardinalities. -/
theorem fixedColumnWordRepresentations_spec {N k : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r s : Real) (a : ColumnAnchorTuple N k)
    (hident : ∀ v ∈ columnWordRepresentations B T L r (columnAnchorList a),
      ColumnWordIdentity T L s (columnAnchorList a) v)
    {w : ColumnWord N (k+1)} (hw : w ∈ fixedColumnWordRepresentations B T L r a) :
    (∀ x ∈ columnWordEntries w, x ∈ B) ∧
      columnWordValue w = columnAnchorEval id (columnAnchorList a) ∧
      ColumnListIdentity T L s (columnAnchorList a) (columnWordEntries w) := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hw
  have hs := columnWordRepresentations_spec B T L r (columnAnchorList a) v hv
  change (∀ x ∈ columnWordEntries (columnWordLengthEquiv _ v), x ∈ B) ∧
    columnWordValue (columnWordLengthEquiv _ v) = _ ∧
    ColumnListIdentity T L s _ (columnWordEntries (columnWordLengthEquiv _ v))
  rw [columnWordLengthEquiv_entries]
  refine ⟨columnWordEntries_mem B v hs.1,?_,(hident v hv).to_list⟩
  exact (columnWordLengthEquiv_eval _ id v).trans hs.2.1

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs16HigherArrangementErrorBudget

/-! Eight-column relation failures are tested on the actual common
quarter-radius Bohr domain of their four difference maps. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnTuplePairs {N : Nat} (v : Fin 8 → ZMod N) (j : Fin 4) : ZMod N × ZMod N :=
  (v ⟨2*j.val,by omega⟩,v ⟨2*j.val+1,by omega⟩)
def columnTupleFrequencies {N : Nat} (T : ZMod N → Finset (ZMod N))
    (v : Fin 8 → ZMod N) : Finset (ZMod N) :=
  Finset.univ.biUnion fun j : Fin 4 => columnDifferenceSpectrum T (columnTuplePairs v j)
def ColumnTupleRespected {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (v : Fin 8 → ZMod N) : Prop :=
  ∀ z ∈ bohr (columnTupleFrequencies T v) (r/4), ColumnDifferenceQuadruple L (columnTuplePairs v) z

def columnTupleFailures {N : Nat} [NeZero N] (V : Finset (Fin 8 → ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) (r : Real) :
    Finset (Fin 8 → ZMod N) := V.filter fun v => ¬ ColumnTupleRespected T L r v

def incompatibleAnchorQuadruples {N : Nat} [NeZero N] (C : Finset (Fin 4 → ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) (r : Real) :
    Finset (Fin 4 → ZMod N) :=
  C.filter fun q => ¬ ColumnPairCompatible T L r (q 0,q 1) (q 2,q 3)

theorem columnTuplePairs_left {N : Nat} (p : HigherArrangementParameter N) (j : Fin 4) :
    columnTuplePairs (higherArrangementLeftColumns p) j =
      higherArrangementEndpointPair p (Fin.castAdd 4 j) := by
  fin_cases j <;> rfl

theorem columnTuplePairs_right {N : Nat} (p : HigherArrangementParameter N) (j : Fin 4) :
    columnTuplePairs (higherArrangementRightColumns p) j =
      higherArrangementEndpointPair p (Fin.natAdd 4 j) := by
  fin_cases j <;> rfl

theorem columnTupleFrequencies_left {N : Nat} (T : ZMod N → Finset (ZMod N))
    (p : HigherArrangementParameter N) :
    columnTupleFrequencies T (higherArrangementLeftColumns p) =
      higherLeftFrequencies T (higherArrangementEndpoints p) := by
  simp only [columnTupleFrequencies,columnTuplePairs_left,higherLeftFrequencies_eq_pair_union]

theorem columnTupleFrequencies_right {N : Nat} (T : ZMod N → Finset (ZMod N))
    (p : HigherArrangementParameter N) :
    columnTupleFrequencies T (higherArrangementRightColumns p) =
      higherRightFrequencies T (higherArrangementEndpoints p) := by
  simp only [columnTupleFrequencies,columnTuplePairs_right,higherRightFrequencies_eq_pair_union]

theorem columnTupleRespected_left_iff {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (p : HigherArrangementParameter N) :
    ColumnTupleRespected T L r (higherArrangementLeftColumns p) ↔
      ∀ z ∈ bohr (higherLeftFrequencies T (higherArrangementEndpoints p)) (r/4),
        ColumnDifferenceQuadruple L (fun j : Fin 4 => higherArrangementEndpointPair p (Fin.castAdd 4 j)) z := by
  simp only [ColumnTupleRespected,columnTupleFrequencies_left,ColumnDifferenceQuadruple,columnTuplePairs_left]

theorem columnTupleRespected_right_iff {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (p : HigherArrangementParameter N) :
    ColumnTupleRespected T L r (higherArrangementRightColumns p) ↔
      ∀ z ∈ bohr (higherRightFrequencies T (higherArrangementEndpoints p)) (r/4),
        ColumnDifferenceQuadruple L (fun j : Fin 4 => higherArrangementEndpointPair p (Fin.natAdd 4 j)) z := by
  simp only [ColumnTupleRespected,columnTupleFrequencies_right,ColumnDifferenceQuadruple,columnTuplePairs_right]

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs16ColumnTupleRelations

/-! Remove the actual compatibility, column-relation, and simultaneous
selection failure sets. Every retained arrangement then supplies all
hypotheses needed for the coherent-anchor theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def jointGoodHigherArrangements {N : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N)) (C : Finset (Fin 4 → ZMod N))
    (V : Finset (Fin 8 → ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (s : PairSelectionState N) (d : Nat) (r : Real) :
    Finset (HigherArrangementParameter N) :=
  higherArrangementAvoidingBadData H (jointHigherFailures H T s d r)
    (incompatibleAnchorQuadruples C T L r ∪ jointQuadrupleFailures C T s d r)
    (columnTupleFailures V T L r) (columnTupleFailures V T L r)

theorem jointGoodHigherArrangements_good {N d : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N)) (C : Finset (Fin 4 → ZMod N))
    (V : Finset (Fin 8 → ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (s : PairSelectionState N) (r : Real)
    (hC : ∀ p ∈ H, ∀ j, higherArrangementAnchorQuadruple p j ∈ C)
    (hV : ∀ p ∈ H, higherArrangementLeftColumns p ∈ V ∧ higherArrangementRightColumns p ∈ V)
    {p : HigherArrangementParameter N} (hp : p ∈ jointGoodHigherArrangements H C V T L s d r) :
    GoodHigherAnchorArrangement T s.frequencies L r (jointSelectionRadius d r) p := by
  obtain ⟨hpH,hquad,hleft,hright,hhigher⟩ :=
    (mem_higherArrangementAvoidingBadData H _ _ _ _ p).mp hp
  have hcomp (j : Fin 4) : ColumnPairCompatible T L r
      (higherArrangementEndpointPair p (Fin.castAdd 4 j))
      (higherArrangementEndpointPair p (Fin.natAdd 4 j)) := by
    by_contra hn
    apply hquad j
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hC p hpH j,hn⟩
  have hpair (j : Fin 4) :
      bohr (s.frequencies (higherArrangementEndpointPair p (Fin.castAdd 4 j)) ∪
        s.frequencies (higherArrangementEndpointPair p (Fin.natAdd 4 j))) (jointSelectionRadius d r) ⊆
      bohrQuarterSum (columnDifferenceSpectrum T (higherArrangementEndpointPair p (Fin.castAdd 4 j)))
        (columnDifferenceSpectrum T (higherArrangementEndpointPair p (Fin.natAdd 4 j))) r := by
    by_contra hn
    apply hquad j
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hC p hpH j,hn⟩
  have hcontain : bohr (higherSelectedPairFrequencies s.frequencies p) (jointSelectionRadius d r) ⊆
      bohrQuarterSum (higherLeftFrequencies T (higherArrangementEndpoints p))
        (higherRightFrequencies T (higherArrangementEndpoints p)) r := by
    by_contra hn
    exact hhigher (Finset.mem_filter.mpr ⟨hpH,hn⟩)
  have hL : ColumnTupleRespected T L r (higherArrangementLeftColumns p) := by
    by_contra hn
    exact hleft (Finset.mem_filter.mpr ⟨(hV p hpH).1,hn⟩)
  have hR : ColumnTupleRespected T L r (higherArrangementRightColumns p) := by
    by_contra hn
    exact hright (Finset.mem_filter.mpr ⟨(hV p hpH).2,hn⟩)
  exact ⟨hcomp,hpair,hcontain,(columnTupleRespected_left_iff T L r p).mp hL,
    (columnTupleRespected_right_iff T L r p).mp hR⟩

theorem jointGoodHigherArrangements_mass {N d : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N)) (C : Finset (Fin 4 → ZMod N))
    (V : Finset (Fin 8 → ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (s : PairSelectionState N) {r kappa eps eta delta : Real}
    (hH : kappa*(N : Real)^11 ≤ H.card)
    (hcompat : ((incompatibleAnchorQuadruples C T L r).card : Real) ≤ eps*(N : Real)^3)
    (hrel : ((columnTupleFailures V T L r).card : Real) ≤ eta*(N : Real)^7)
    (hquad : ((jointQuadrupleFailures C T s d r).card : Real) ≤ delta*(N : Real)^3)
    (hhigher : ((jointHigherFailures H T s d r).card : Real) ≤ delta*(N : Real)^11) :
    (kappa-4*eps-2*eta-5*delta)*(N : Real)^11 ≤
      (jointGoodHigherArrangements H C V T L s d r).card := by
  have hE : (((incompatibleAnchorQuadruples C T L r ∪ jointQuadrupleFailures C T s d r).card) : Real) ≤
      (eps+delta)*(N : Real)^3 := by
    have hu : (((incompatibleAnchorQuadruples C T L r ∪ jointQuadrupleFailures C T s d r).card) : Real) ≤
        ((incompatibleAnchorQuadruples C T L r).card : Real)+((jointQuadrupleFailures C T s d r).card : Real) := by
      exact_mod_cast Finset.card_union_le (incompatibleAnchorQuadruples C T L r) (jointQuadrupleFailures C T s d r)
    nlinarith only [hu,hcompat,hquad]
  have h := higher_arrangements_avoiding_bad_data_mass H (jointHigherFailures H T s d r)
    (incompatibleAnchorQuadruples C T L r ∪ jointQuadrupleFailures C T s d r)
    (columnTupleFailures V T L r) (columnTupleFailures V T L r) hH hE hrel hrel hhigher
  have he : kappa-4*(eps+delta)-eta-eta-delta = kappa-4*eps-2*eta-5*delta := by ring
  simpa only [he,jointGoodHigherArrangements] using h

end LeanProofs.GowersSzemeredi

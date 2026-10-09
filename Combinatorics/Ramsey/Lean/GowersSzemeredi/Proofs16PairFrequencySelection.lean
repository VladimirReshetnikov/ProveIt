import GowersSzemeredi.Proofs16PairSelectionIndices

/-! A finite family of controlled Freiman maps makes all but a specified
number of additive quadruples satisfy the required pair containment. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def indexedPairFrequencies {N m : Nat} (g : Fin m → PairFrequencyMap N)
    (I : (ZMod N × ZMod N) → Finset (Fin m)) (p : ZMod N × ZMod N) : Finset (ZMod N) :=
  (I p).image fun i => (g i).toFun (p.1-p.2)

theorem pair_frequency_selection {N d : Nat} [NeZero N] [Fact N.Prime]
    (C : Finset (Fin 4 → ZMod N)) (T : ZMod N → Finset (ZMod N)) {delta r : Real}
    (hd : 0 < delta) (hr : 0 < r) (hr4 : r < 4)
    (hT : ∀ x, (T x).card ≤ d) (hadd : ∀ q ∈ C, q 0-q 1 = q 2-q 3) :
    ∃ (m : Nat) (g : Fin m → PairFrequencyMap N) (I : (ZMod N × ZMod N) → Finset (Fin m)),
      (m : Real)*pairSelectionGain delta d r ≤ pairSelectionRank d r ∧
      (∀ i, (g i).Controlled (escapingFreimanDensity delta d r)) ∧
      (∀ p, (I p).card ≤ pairSelectionRank d r ∧
        (indexedPairFrequencies g I p).card = (I p).card ∧
        (∀ i ∈ I p, p.1-p.2 ∈ (g i).domain) ∧
        AddDissociated (indexedPairFrequencies g I p : Set (ZMod N)) ∧
        indexedPairFrequencies g I p ⊆
          boundedFrequencySpan (fun b : ↥(T p.1 ∪ T p.2) => (b : ZMod N)) (pairSelectionCutoff d r)) ∧
      ((C.filter fun q => ¬ bohr (pairSelectedQuadrupleFrequencies (indexedPairFrequencies g I) q)
        (pairSelectionRadius d r) ⊆ bohrQuarterSum (T (q 0) ∪ T (q 1)) (T (q 2) ∪ T (q 3)) r).card : Real)
        < delta*(N : Real)^3 := by
  obtain ⟨s,hs,hbad,hcount⟩ := exists_pair_frequency_selection C T hd hr hr4 hT hadd
  obtain ⟨I,hI⟩ := s.index_family T hs
  let g : Fin s.maps.length → PairFrequencyMap N := s.maps.get
  have heq : indexedPairFrequencies g I = s.frequencies := by
    funext p
    exact (hI p).2.1
  refine ⟨s.maps.length,g,I,hcount,?_,?_,?_⟩
  · intro i
    exact hs.1 (g i) (List.get_mem _ _)
  · intro p
    refine ⟨?_,?_,(hI p).2.2,?_,?_⟩
    · rw [(hI p).1]
      exact pair_selection_frequency_card_bound T s.frequencies r hT
        (fun p => (hs.2.1 p).1) (fun p => (hs.2.1 p).2) p
    · rw [heq]
      exact (hI p).1.symm
    · rw [heq]
      exact (hs.2.1 p).1
    · rw [heq]
      exact (hs.2.1 p).2
  · simpa only [heq,pairSelectionFailures] using hbad

end LeanProofs.GowersSzemeredi

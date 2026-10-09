import GowersSzemeredi.Proofs16JointSelectionIndices
import GowersSzemeredi.Proofs16PairFrequencySelection

/-! One finite family of controlled Freiman maps simultaneously makes both
quadruple and higher-arrangement containment failures sparse. Actual
map indices, domain memberships and frequency-set cardinalities agree. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem joint_frequency_selection {N d : Nat} [NeZero N] [Fact N.Prime]
    (C : Finset (Fin 4 → ZMod N)) (H : Finset (HigherArrangementParameter N))
    (T : ZMod N → Finset (ZMod N)) {delta r : Real}
    (hd : 0 < delta) (hr : 0 < r) (hr4 : r < 4)
    (hT : ∀ x, (T x).card ≤ d) (hadd : ∀ q ∈ C, q 0-q 1 = q 2-q 3) :
    ∃ (m : Nat) (g : Fin m → PairFrequencyMap N) (I : (ZMod N × ZMod N) → Finset (Fin m)),
      (m : Real)*jointSelectionGain delta d r ≤ jointSelectionRank d r ∧
      (∀ i, (g i).JointControlled delta d r) ∧
      (∀ p, (I p).card ≤ jointSelectionRank d r ∧
        (indexedPairFrequencies g I p).card = (I p).card ∧
        (∀ i ∈ I p, p.1-p.2 ∈ (g i).domain) ∧
        AddDissociated (indexedPairFrequencies g I p : Set (ZMod N)) ∧
        indexedPairFrequencies g I p ⊆
          boundedFrequencySpan (fun b : ↥(T p.1 ∪ T p.2) => (b : ZMod N)) (jointSelectionCutoff d r)) ∧
      ((C.filter fun q => ¬ bohr (pairSelectedQuadrupleFrequencies (indexedPairFrequencies g I) q)
        (jointSelectionRadius d r) ⊆ bohrQuarterSum (T (q 0) ∪ T (q 1)) (T (q 2) ∪ T (q 3)) r).card : Real)
        < delta*(N : Real)^3 ∧
      ((H.filter fun p => ¬ bohr (higherSelectedPairFrequencies (indexedPairFrequencies g I) p)
        (jointSelectionRadius d r) ⊆ bohrQuarterSum
          (higherLeftFrequencies T (higherArrangementEndpoints p))
          (higherRightFrequencies T (higherArrangementEndpoints p)) r).card : Real)
        < delta*(N : Real)^11 := by
  obtain ⟨s,hs,hbad,hhigher,hcount⟩ := exists_joint_frequency_selection C H T hd hr hr4 hT hadd
  obtain ⟨I,hI⟩ := s.joint_index_family T hs
  let g : Fin s.maps.length → PairFrequencyMap N := s.maps.get
  have heq : indexedPairFrequencies g I = s.frequencies := by
    funext p
    exact (hI p).2.1
  refine ⟨s.maps.length,g,I,hcount,?_,?_,?_,?_⟩
  · intro i
    exact hs.1 (g i) (List.get_mem _ _)
  · intro p
    refine ⟨?_,?_,(hI p).2.2,?_,?_⟩
    · rw [(hI p).1]
      exact higher_pair_frequency_card_bound T s.frequencies hT
        (fun p => (hs.2.1 p).1) (fun p => (hs.2.1 p).2) p
    · rw [heq]
      exact (hI p).1.symm
    · rw [heq]
      exact (hs.2.1 p).1
    · rw [heq]
      exact (hs.2.1 p).2
  · simpa only [heq,jointQuadrupleFailures] using hbad
  · simpa only [heq,jointHigherFailures] using hhigher

end LeanProofs.GowersSzemeredi

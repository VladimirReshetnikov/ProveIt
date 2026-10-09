import GowersSzemeredi.Proofs16HigherEscapingPairMaps
import GowersSzemeredi.Proofs16HigherArrangementPairProjection

/-! Escape of the sum from the coefficient-four span forces one of the
four left pair values to escape its own unit span. Repeated frequencies
across different pair selections are allowed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem higher_left_pair_escape {N : Nat} [NeZero N]
    (f : Fin 16 → ZMod N → ZMod N) (theta : Fin 8 → PairFrequencyMap N)
    (T : ZMod N → Finset (ZMod N)) (F : (ZMod N × ZMod N) → Finset (ZMod N))
    (D : Finset (ZMod N)) (p : HigherArrangementParameter N) (R : Nat)
    (hf : ∀ i x, f i x ∈ boundedFrequencySpan (fun a : T x => (a : ZMod N)) R)
    (hFD : ∀ j : Fin 4, F (higherArrangementEndpointPair p (Fin.castAdd 4 j)) ⊆ D)
    (hvalue : ∀ j, higherArrangementPairDifference p j ∈ (theta j).domain ∧
      (theta j).toFun (higherArrangementPairDifference p j) = higherArrangementPairValue f p j)
    (hescape : higherLeftPairMapValue theta p ∉ boundedFrequencySpan (fun a : D => (a : ZMod N)) 4) :
    ∃ j : Fin 4,
      let i := Fin.castAdd 4 j
      let e := higherArrangementEndpointPair p i
      higherArrangementPairDifference p i ∈ (theta i).domain ∧
      (theta i).toFun (higherArrangementPairDifference p i) ∈
        boundedFrequencySpan (fun a : ↥(T e.1 ∪ T e.2) => (a : ZMod N)) (2*R) ∧
      (theta i).toFun (higherArrangementPairDifference p i) ∉
        boundedFrequencySpan (fun a : F e => (a : ZMod N)) 1 := by
  have hex : ∃ j : Fin 4, (theta (Fin.castAdd 4 j)).toFun (higherArrangementPairDifference p (Fin.castAdd 4 j)) ∉
      boundedFrequencySpan (fun a : F (higherArrangementEndpointPair p (Fin.castAdd 4 j)) => (a : ZMod N)) 1 := by
    by_contra hn
    push Not at hn
    have hsum := sum_mem_boundedFrequencySpan D 1 (Finset.univ : Finset (Fin 4))
      (fun j => (theta (Fin.castAdd 4 j)).toFun (higherArrangementPairDifference p (Fin.castAdd 4 j)))
      (fun j _ => boundedFrequencySpan_mono_generators _ D 1 (hFD j) (hn j))
    apply hescape
    simpa only [higherLeftPairMapValue,Finset.card_univ,Fintype.card_fin,Nat.mul_one] using hsum
  obtain ⟨j,hj⟩ := hex
  refine ⟨j,(hvalue _).1,?_,hj⟩
  rw [(hvalue _).2]
  have h := sub_mem_union_boundedFrequencySpan
    (T (higherArrangementEndpoints p (higherArrangementPairLeft (Fin.castAdd 4 j))))
    (T (higherArrangementEndpoints p (higherArrangementPairRight (Fin.castAdd 4 j)))) R R
    (hf (higherArrangementPairLeft (Fin.castAdd 4 j)) _)
    (hf (higherArrangementPairRight (Fin.castAdd 4 j)) _)
  simpa only [higherArrangementPairValue,higherArrangementEndpointPair,two_mul] using h

end LeanProofs.GowersSzemeredi

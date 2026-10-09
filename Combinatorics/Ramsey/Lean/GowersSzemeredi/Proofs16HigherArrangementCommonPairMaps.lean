import GowersSzemeredi.Proofs16HigherArrangementPairFamily
import GowersSzemeredi.Proofs16HigherArrangementFreimanFamily

/-! Combine all sixteen coordinate extractions with all eight pair-map
alignments. Every restriction applies to one original arrangement family,
and the original eight-term equation survives as an equation of maps. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def HigherArrangementPairMapEquation {N : Nat} (theta : Fin 8 → PairFrequencyMap N)
    (p : HigherArrangementParameter N) : Prop :=
  (theta 0).toFun (higherArrangementPairDifference p 0)+
    (theta 1).toFun (higherArrangementPairDifference p 1)+
    (theta 2).toFun (higherArrangementPairDifference p 2)+
    (theta 3).toFun (higherArrangementPairDifference p 3) =
  (theta 4).toFun (higherArrangementPairDifference p 4)+
    (theta 5).toFun (higherArrangementPairDifference p 5)+
    (theta 6).toFun (higherArrangementPairDifference p 6)+
    (theta 7).toFun (higherArrangementPairDifference p 7)

theorem higherArrangementPairMapEquation_of_values {N : Nat}
    (f : Fin 16 → ZMod N → ZMod N) (theta : Fin 8 → PairFrequencyMap N)
    (p : HigherArrangementParameter N) (h : HigherArrangementEquation f p)
    (hvalue : ∀ j, (theta j).toFun (higherArrangementPairDifference p j) = higherArrangementPairValue f p j) :
    HigherArrangementPairMapEquation theta p := by
  unfold HigherArrangementPairMapEquation
  simp_rw [hvalue]
  exact h

/-- All sixteen coordinate maps are Freiman and all eight differences
are represented by controlled progression maps on one dense subfamily. -/
theorem higher_arrangements_common_pair_family {N : Nat} [NeZero N] [Fact N.Prime]
    (f : Fin 16 → ZMod N → ZMod N) (Q : Finset (HigherArrangementParameter N))
    (hQ : ∀ p ∈ Q, HigherArrangementEquation f p)
    {delta : Real} (hd : 0 < delta) (hcount : delta*(N : Real)^11 ≤ Q.card) :
    let epsilon := higherArrangementDensity delta 16
    ∃ (E : Fin 16 → Finset (ZMod N)) (theta : Fin 8 → PairFrequencyMap N)
      (R : Finset (HigherArrangementParameter N)),
      R ⊆ Q ∧
      (∀ i, E i ⊆ Q.image (fun p => higherArrangementEndpoints p i) ∧ FreimanHom 8 (E i) (f i)) ∧
      (∀ i, epsilon*N ≤ ((E i).card : Real)) ∧
      (∀ p ∈ R, ∀ i, higherArrangementEndpoints p i ∈ E i) ∧
      (∀ j, ∃ n < 8, (theta j).Controlled ((higherArrangementPairDensity epsilon n)^2)) ∧
      (∀ p ∈ R, ∀ j, higherArrangementPairDifference p j ∈ (theta j).domain ∧
        (theta j).toFun (higherArrangementPairDifference p j) = higherArrangementPairValue f p j) ∧
      (∀ p ∈ R, HigherArrangementPairMapEquation theta p) ∧
      higherArrangementPairDensity epsilon 8*(N : Real)^11 ≤ R.card := by
  obtain ⟨E,S,hSQ,hE,hEsize,hcoords,hS⟩ := higher_arrangements_freiman_family f Q hQ hd hcount
  obtain ⟨theta,R,hRS,hcontrol,hvalue,hR⟩ := higher_arrangements_pair_map_family f E S
    (fun p hp => hQ p (hSQ hp)) (fun i => (hE i).2) hcoords
    (higherArrangementDensity_pos hd 16) hS
  refine ⟨E,theta,R,hRS.trans hSQ,hE,hEsize,fun p hp => hcoords p (hRS hp),
    hcontrol,hvalue,?_,hR⟩
  intro p hp
  exact higherArrangementPairMapEquation_of_values f theta p (hQ p (hSQ (hRS hp)))
    (fun j => (hvalue p hp j).2)

end LeanProofs.GowersSzemeredi

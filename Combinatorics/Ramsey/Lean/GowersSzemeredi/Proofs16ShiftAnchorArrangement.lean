import GowersSzemeredi.Proofs16JointSelectedGluing

/-! Anchor functions are indexed by the shift. Repeated shifts therefore
use the same anchors, as required for one globally defined local map. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def shiftAnchorPair {N : Nat} (x : ZMod N → ZMod N) (a : ZMod N) : ZMod N × ZMod N :=
  (x a+a,x a)

def shiftAnchorArrangement {N : Nat} (x y : ZMod N → ZMod N)
    (a : Fin 4 → ZMod N) : HigherArrangementParameter N :=
  ((a 0,![a 1,a 2,x (a 1),x (a 2),x (a 3),y (a 0),y (a 1),y (a 2),y (a 3)]),x (a 0))

theorem shiftAnchorArrangement_left_pair {N : Nat} (x y : ZMod N → ZMod N)
    (a : Fin 4 → ZMod N) (ha : a 0+a 1 = a 2+a 3) (j : Fin 4) :
    higherArrangementEndpointPair (shiftAnchorArrangement x y a) (Fin.castAdd 4 j) = shiftAnchorPair x (a j) := by
  have h3 : a 0+a 1-a 2 = a 3 := by linear_combination ha
  fin_cases j <;> dsimp [shiftAnchorArrangement,higherArrangementEndpointPair,higherArrangementEndpoints,
    higherArrangementPairLeft,higherArrangementPairRight,shiftAnchorPair]
  simp only [h3]

theorem shiftAnchorArrangement_right_pair {N : Nat} (x y : ZMod N → ZMod N)
    (a : Fin 4 → ZMod N) (ha : a 0+a 1 = a 2+a 3) (j : Fin 4) :
    higherArrangementEndpointPair (shiftAnchorArrangement x y a) (Fin.natAdd 4 j) = shiftAnchorPair y (a j) := by
  have h3 : a 0+a 1-a 2 = a 3 := by linear_combination ha
  fin_cases j <;> dsimp [shiftAnchorArrangement,higherArrangementEndpointPair,higherArrangementEndpoints,
    higherArrangementPairLeft,higherArrangementPairRight,shiftAnchorPair]
  simp only [h3]

def shiftAnchorFrequencies {N : Nat} (F : (ZMod N × ZMod N) → Finset (ZMod N))
    (x y : ZMod N → ZMod N) (a : ZMod N) : Finset (ZMod N) :=
  F (shiftAnchorPair x a) ∪ F (shiftAnchorPair y a)

theorem shiftAnchorArrangement_selected_frequencies {N : Nat}
    (F : (ZMod N × ZMod N) → Finset (ZMod N)) (x y : ZMod N → ZMod N)
    (a : Fin 4 → ZMod N) (ha : a 0+a 1 = a 2+a 3) :
    higherSelectedPairFrequencies F (shiftAnchorArrangement x y a) =
      Finset.univ.biUnion (fun j : Fin 4 => shiftAnchorFrequencies F x y (a j)) := by
  rw [higherSelectedPairFrequencies_eq_anchor_union]
  simp_rw [shiftAnchorArrangement_left_pair x y a ha,shiftAnchorArrangement_right_pair x y a ha]
  rfl

end LeanProofs.GowersSzemeredi

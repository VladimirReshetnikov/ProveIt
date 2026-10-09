import GowersSzemeredi.Proofs16BoundedIndexSelection

/-! The four anchor maps use at most eight pair-index sets. Their union
has size at most eight times the selected pair rank. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def shiftAnchorIndices {N m : Nat} (I : (ZMod N × ZMod N) → Finset (Fin m))
    (x y : ZMod N → ZMod N) (a : ZMod N) : Finset (Fin m) :=
  I (shiftAnchorPair x a) ∪ I (shiftAnchorPair y a)
def anchorQuadrupleIndices {N m : Nat} (I : (ZMod N × ZMod N) → Finset (Fin m))
    (x y : ZMod N → ZMod N) (a : Fin 4 → ZMod N) : Finset (Fin m) :=
  Finset.univ.biUnion fun j : Fin 4 => shiftAnchorIndices I x y (a j)

theorem anchorQuadrupleIndices_card_le {N m K : Nat}
    (I : (ZMod N × ZMod N) → Finset (Fin m)) (x y : ZMod N → ZMod N)
    (hI : ∀ p, (I p).card ≤ K) (a : Fin 4 → ZMod N) :
    (anchorQuadrupleIndices I x y a).card ≤ 8*K := by
  have hj (j : Fin 4) : (shiftAnchorIndices I x y (a j)).card ≤ 2*K := by
    have h := Finset.card_union_le (I (shiftAnchorPair x (a j))) (I (shiftAnchorPair y (a j)))
    have hx := hI (shiftAnchorPair x (a j))
    have hy := hI (shiftAnchorPair y (a j))
    unfold shiftAnchorIndices
    omega
  calc (anchorQuadrupleIndices I x y a).card ≤
      ∑ j : Fin 4, (shiftAnchorIndices I x y (a j)).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin 4, 2*K := Finset.sum_le_sum fun j _ => hj j
    _ = _ := by simp; ring

theorem shiftAnchorIndices_subset_quadruple {N m : Nat}
    (I : (ZMod N × ZMod N) → Finset (Fin m)) (x y : ZMod N → ZMod N)
    (a : Fin 4 → ZMod N) (j : Fin 4) :
    shiftAnchorIndices I x y (a j) ⊆ anchorQuadrupleIndices I x y a := by
  intro i hi
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hi⟩

theorem shiftAnchorIndices_image {N : Nat} [NeZero N] (s : PairSelectionState N)
    (I : (ZMod N × ZMod N) → Finset (Fin s.maps.length))
    (hI : ∀ p, (I p).image (fun i => (s.maps.get i).toFun (p.1-p.2)) = s.frequencies p)
    (x y : ZMod N → ZMod N) (a : ZMod N) :
    (shiftAnchorIndices I x y a).image (fun i => (s.maps.get i).toFun a) =
      shiftAnchorFrequencies s.frequencies x y a := by
  have hx := hI (shiftAnchorPair x a)
  have hy := hI (shiftAnchorPair y a)
  simp only [shiftAnchorPair,add_sub_cancel_left] at hx hy
  simp only [shiftAnchorIndices,shiftAnchorFrequencies,Finset.image_union,shiftAnchorPair,hx,hy]

theorem shiftAnchorIndices_domain {N : Nat} [NeZero N] (s : PairSelectionState N)
    (I : (ZMod N × ZMod N) → Finset (Fin s.maps.length))
    (hI : ∀ p, ∀ i ∈ I p, p.1-p.2 ∈ (s.maps.get i).domain)
    (x y : ZMod N → ZMod N) (a : ZMod N) :
    ∀ i ∈ shiftAnchorIndices I x y a, a ∈ (s.maps.get i).domain := by
  intro i hi
  rcases Finset.mem_union.mp hi with hx | hy
  · simpa only [shiftAnchorPair,add_sub_cancel_left] using hI (shiftAnchorPair x a) i hx
  · simpa only [shiftAnchorPair,add_sub_cancel_left] using hI (shiftAnchorPair y a) i hy

end LeanProofs.GowersSzemeredi

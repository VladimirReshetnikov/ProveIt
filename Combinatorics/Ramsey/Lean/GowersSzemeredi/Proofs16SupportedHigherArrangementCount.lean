import GowersSzemeredi.Proofs16HigherArrangementReconstruction

/-! Every dense column set supports many higher arrangements. Two
second-moment bounds retain all multiplicities and give density `alpha^16`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def supportedHigherArrangements {N : Nat} [NeZero N] (W : Finset (ZMod N)) :
    Finset (HigherArrangementParameter N) :=
  Finset.univ.filter fun p => ∀ i, higherArrangementEndpoints p i ∈ W

theorem supported_higher_arrangements_lift_card {N : Nat} [NeZero N]
    (W : Finset (ZMod N)) :
    (mappedAdditiveQuadruples (supportedAnchorQuadruples W) (fun q => q 0-q 1)).card ≤
      (supportedHigherArrangements W).card := by
  let J := mappedAdditiveQuadruples (supportedAnchorQuadruples W) (fun q => q 0-q 1)
  have hquad (q : Fin 4 → Fin 4 → ZMod N) (hq : q ∈ J) : ∀ j, q j 0-q j 1 = q j 2-q j 3 := by
    intro j
    exact (Finset.mem_filter.mp ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hq).1) j)).2
  have hshift (q : Fin 4 → Fin 4 → ZMod N) (hq : q ∈ J) :
      (q 0 0-q 0 1)+(q 1 0-q 1 1) = (q 2 0-q 2 1)+(q 3 0-q 3 1) :=
    (Finset.mem_filter.mp hq).2
  change J.card ≤ _
  apply Finset.card_le_card_of_injOn higherArrangementOfAnchorQuadruples
  · intro q hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    apply higherArrangement_endpoints_mem_of_anchor_quadruples W
    intro j i
    rw [higherArrangementOfAnchorQuadruples_reconstruct q (hquad q hq) (hshift q hq)]
    exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp
      (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hq).1 j)).1 i
  · intro q hq t ht he
    funext j
    calc q j = higherArrangementAnchorQuadruple (higherArrangementOfAnchorQuadruples q) j :=
           (higherArrangementOfAnchorQuadruples_reconstruct q (hquad q hq) (hshift q hq) j).symm
      _ = higherArrangementAnchorQuadruple (higherArrangementOfAnchorQuadruples t) j := by rw [he]
      _ = t j := higherArrangementOfAnchorQuadruples_reconstruct t (hquad t ht) (hshift t ht) j

theorem card_sixteen_le_supported_higher_arrangements {N : Nat} [NeZero N]
    (W : Finset (ZMod N)) : W.card^16 ≤ (supportedHigherArrangements W).card*N^5 := by
  let C := supportedAnchorQuadruples W
  have h1 : W.card^4 ≤ C.card*N := card_four_le_supported_anchor_quadruples W
  have h2 : C.card^4 ≤ (supportedHigherArrangements W).card*N := by
    have hcs := card_four_le_mapped_additive_quadruples C (fun q => q 0-q 1)
    rw [ZMod.card] at hcs
    exact hcs.trans (Nat.mul_le_mul_right N (supported_higher_arrangements_lift_card W))
  calc W.card^16 = (W.card^4)^4 := by ring
    _ ≤ (C.card*N)^4 := Nat.pow_le_pow_left h1 4
    _ = C.card^4*N^4 := by ring
    _ ≤ ((supportedHigherArrangements W).card*N)*N^4 := Nat.mul_le_mul_right _ h2
    _ = _ := by ring

theorem supported_higher_arrangements_dense {N : Nat} [NeZero N]
    (W : Finset (ZMod N)) {alpha : Real} (ha : 0 ≤ alpha)
    (hW : alpha*(N : Real) ≤ W.card) :
    alpha^16*(N : Real)^11 ≤ (supportedHigherArrangements W).card := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hc : (W.card : Real)^16 ≤ (supportedHigherArrangements W).card*(N : Real)^5 := by
    exact_mod_cast card_sixteen_le_supported_higher_arrangements W
  have hp := pow_le_pow_left₀ (show 0 ≤ alpha*(N : Real) by positivity) hW 16
  apply le_of_mul_le_mul_right (a := (N : Real)^5) _ (by positivity)
  calc alpha^16*(N : Real)^11*(N : Real)^5 = (alpha*(N : Real))^16 := by ring
    _ ≤ (W.card : Real)^16 := hp
    _ ≤ _ := hc

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs16AnchorIndexSets

/-! Choose one small index set for a positive fraction of the actual
anchor quadruples. This preserves all their previously established
relations, not merely a dense set of individual shifts. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem joint_anchor_common_indices {N d : Nat} [NeZero N]
    (s : PairSelectionState N) (T : ZMod N → Finset (ZMod N)) {delta r : Real}
    (hT : ∀ x, (T x).card ≤ d) (hs : s.JointValid T delta d r)
    (x y : ZMod N → ZMod N) (Q : Finset (Fin 4 → ZMod N)) (hQ : Q.Nonempty) :
    ∃ (I : (ZMod N × ZMod N) → Finset (Fin s.maps.length))
      (J : Finset (Fin s.maps.length)) (R : Finset (Fin 4 → ZMod N)),
      (∀ p, (I p).card = (s.frequencies p).card ∧
        (I p).image (fun i => (s.maps.get i).toFun (p.1-p.2)) = s.frequencies p ∧
        ∀ i ∈ I p, p.1-p.2 ∈ (s.maps.get i).domain) ∧
      J.card ≤ 8*jointSelectionRank d r ∧ R ⊆ Q ∧
      Q.card ≤ (s.maps.length+1)^(8*jointSelectionRank d r)*R.card ∧ R.Nonempty ∧
      ∀ a ∈ R, anchorQuadrupleIndices I x y a = J ∧
        ∀ j : Fin 4, shiftAnchorIndices I x y (a j) ⊆ J ∧
          shiftAnchorFrequencies s.frequencies x y (a j) ⊆ J.image (fun i => (s.maps.get i).toFun (a j)) := by
  obtain ⟨I,hI⟩ := s.joint_index_family T hs
  have hcap (p : ZMod N × ZMod N) : (I p).card ≤ jointSelectionRank d r := by
    rw [(hI p).1]
    exact higher_pair_frequency_card_bound T s.frequencies hT (fun p => (hs.2.1 p).1)
      (fun p => (hs.2.1 p).2) p
  obtain ⟨J,R,hJ,hRQ,hcount,hR,hcodes⟩ := exists_common_bounded_index_set Q
    (anchorQuadrupleIndices I x y) hQ (fun a _ => anchorQuadrupleIndices_card_le I x y hcap a)
  refine ⟨I,J,R,hI,hJ,hRQ,hcount,hR,?_⟩
  intro a ha
  refine ⟨hcodes a ha,?_⟩
  intro j
  have hsub : shiftAnchorIndices I x y (a j) ⊆ J := by
    rw [← hcodes a ha]
    exact shiftAnchorIndices_subset_quadruple I x y a j
  refine ⟨hsub,?_⟩
  rw [← shiftAnchorIndices_image s I (fun p => (hI p).2.1) x y (a j)]
  exact Finset.image_subset_image hsub

end LeanProofs.GowersSzemeredi

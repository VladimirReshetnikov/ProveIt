import GowersSzemeredi.Proofs16BoundedIndexPatterns

/-! Exact index patterns retain every selected map's domain membership
at its own position. Each position needs only twice the pair rank. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem joint_anchor_row_indices {N d : Nat} [NeZero N]
    (s : PairSelectionState N) (T : ZMod N → Finset (ZMod N)) {delta r : Real}
    (hT : ∀ x, (T x).card ≤ d) (hs : s.JointValid T delta d r)
    (x y : ZMod N → ZMod N) (Q : Finset (Fin 4 → ZMod N)) (hQ : Q.Nonempty) :
    ∃ (J : Fin 4 → Finset (Fin s.maps.length)) (R : Finset (Fin 4 → ZMod N)),
      (∀ j, (J j).card ≤ 2*jointSelectionRank d r) ∧ R ⊆ Q ∧
      Q.card ≤ (s.maps.length+1)^(8*jointSelectionRank d r)*R.card ∧ R.Nonempty ∧
      ∀ a ∈ R, ∀ j : Fin 4,
        (J j).image (fun i => (s.maps.get i).toFun (a j)) = shiftAnchorFrequencies s.frequencies x y (a j) ∧
        ∀ i ∈ J j, a j ∈ (s.maps.get i).domain := by
  obtain ⟨I,hI⟩ := s.joint_index_family T hs
  have hcap (p : ZMod N × ZMod N) : (I p).card ≤ jointSelectionRank d r := by
    rw [(hI p).1]
    exact higher_pair_frequency_card_bound T s.frequencies hT (fun p => (hs.2.1 p).1)
      (fun p => (hs.2.1 p).2) p
  have hsize (a : ZMod N) : (shiftAnchorIndices I x y a).card ≤ 2*jointSelectionRank d r := by
    have h := Finset.card_union_le (I (shiftAnchorPair x a)) (I (shiftAnchorPair y a))
    have hx := hcap (shiftAnchorPair x a)
    have hy := hcap (shiftAnchorPair y a)
    unfold shiftAnchorIndices
    omega
  obtain ⟨J,R,hJ,hRQ,hcount,hR,hcodes⟩ := exists_common_bounded_index_pattern Q
    (fun a j => shiftAnchorIndices I x y (a j)) hQ (fun a _ j => hsize (a j))
  have he : 2*jointSelectionRank d r*4 = 8*jointSelectionRank d r := by omega
  refine ⟨J,R,hJ,hRQ,by simpa only [he] using hcount,hR,?_⟩
  intro a ha j
  have hcode := congrFun (hcodes a ha) j
  rw [← hcode]
  exact ⟨shiftAnchorIndices_image s I (fun p => (hI p).2.1) x y (a j),
    shiftAnchorIndices_domain s I (fun p => (hI p).2.2) x y (a j)⟩

end LeanProofs.GowersSzemeredi

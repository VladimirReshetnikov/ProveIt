import GowersSzemeredi.Proofs16JointSelectionExtension

/-! Either dense failure family supplies an actual escaping map and
strictly increases the length of the common valid selection state. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem PairSelectionState.improve_joint_quadruple {N d : Nat} [NeZero N] [Fact N.Prime]
    (s : PairSelectionState N) (C : Finset (Fin 4 → ZMod N))
    (T : ZMod N → Finset (ZMod N)) {delta r : Real}
    (hd : 0 < delta) (hr : 0 < r) (hr4 : r < 4)
    (hT : ∀ x, (T x).card ≤ d) (hadd : ∀ q ∈ C, q 0-q 1 = q 2-q 3)
    (hs : s.JointValid T delta d r)
    (hbad : delta*(N : Real)^3 ≤ (jointQuadrupleFailures C T s d r).card) :
    ∃ s' : PairSelectionState N, s'.JointValid T delta d r ∧
      s'.maps.length = s.maps.length+1 ∧
      (∀ p, s.frequencies p ⊆ s'.frequencies p) ∧
      ∃ g : PairFrequencyMap N, s'.maps = g :: s.maps := by
  let B := jointQuadrupleFailures C T s d r
  obtain ⟨P,a,theta,E,hPrank,hPproper,hPmass,htheta,_,hE,hvalue⟩ :=
    failed_containments_dense_pair_escape B T (pairSelectedQuadrupleFrequencies s.frequencies)
      s.frequencies hr hr4 hd hbad (fun q hq => hadd q (Finset.mem_filter.mp hq).1) hT
      (fun q _ => joint_selection_quadruple_radius_budget T s.frequencies r hT
        (fun p => (hs.2.1 p).1) (fun p => (hs.2.1 p).2) q)
      (fun _ _ => Finset.subset_union_left) (fun q hq => (Finset.mem_filter.mp hq).2)
  let g : PairFrequencyMap N := ⟨P,a,theta⟩
  have hg : g.JointControlled delta d r := Or.inl ⟨hPrank,hPproper,hPmass,htheta⟩
  have hgain : jointSelectionGain delta d r ≤ pairSelectionGain delta d r := min_le_left _ _
  have hmass : jointSelectionGain delta d r*(N : Real)^2 ≤ E.card :=
    (mul_le_mul_of_nonneg_right hgain (sq_nonneg _)).trans hE
  have hcut : 2*bohrExtensionCutoff (2*d) r ≤ jointSelectionCutoff d r := le_max_left _ _
  obtain ⟨s',hs',hlen,hsub,hlist⟩ := s.extend_joint T hs g E hg hmass (fun p hp =>
    ⟨(hvalue p hp).1,boundedFrequencySpan_mono _ hcut (hvalue p hp).2.1,(hvalue p hp).2.2⟩)
  exact ⟨s',hs',hlen,hsub,g,hlist⟩

theorem PairSelectionState.improve_joint_higher {N d : Nat} [NeZero N] [Fact N.Prime]
    (s : PairSelectionState N) (H : Finset (HigherArrangementParameter N))
    (T : ZMod N → Finset (ZMod N)) {delta r : Real}
    (hd : 0 < delta) (hr : 0 < r) (hr4 : r < 4)
    (hT : ∀ x, (T x).card ≤ d) (hs : s.JointValid T delta d r)
    (hbad : delta*(N : Real)^11 ≤ (jointHigherFailures H T s d r).card) :
    ∃ s' : PairSelectionState N, s'.JointValid T delta d r ∧
      s'.maps.length = s.maps.length+1 ∧
      (∀ p, s.frequencies p ⊆ s'.frequencies p) ∧
      ∃ g : PairFrequencyMap N, s'.maps = g :: s.maps := by
  let B := jointHigherFailures H T s d r
  obtain ⟨j,g,E,hg,_,hE,hvalue⟩ := higher_failed_containments_dense_pair_escape B T
    (higherSelectedPairFrequencies s.frequencies) s.frequencies hr hr4 hd hbad hT
    (fun p _ => higher_pair_selection_radius_budget T s.frequencies hT
      (fun p => (hs.2.1 p).1) (fun p => (hs.2.1 p).2) p)
    (fun p _ j a ha => Finset.mem_biUnion.mpr ⟨Fin.castAdd 4 j,Finset.mem_univ _,ha⟩)
    (fun p hp => (Finset.mem_filter.mp hp).2)
  have hgain : jointSelectionGain delta d r ≤ higherEscapeDensity delta d r/4 := min_le_right _ _
  have hmass : jointSelectionGain delta d r*(N : Real)^2 ≤ E.card :=
    (mul_le_mul_of_nonneg_right hgain (sq_nonneg _)).trans hE
  have hcut : 2*bohrExtensionCutoff (8*d) r ≤ jointSelectionCutoff d r := le_max_right _ _
  obtain ⟨s',hs',hlen,hsub,hlist⟩ := s.extend_joint T hs g E (Or.inr hg) hmass (fun p hp =>
    ⟨(hvalue p hp).1,boundedFrequencySpan_mono _ hcut (hvalue p hp).2.1,(hvalue p hp).2.2⟩)
  exact ⟨s',hs',hlen,hsub,g,hlist⟩

end LeanProofs.GowersSzemeredi

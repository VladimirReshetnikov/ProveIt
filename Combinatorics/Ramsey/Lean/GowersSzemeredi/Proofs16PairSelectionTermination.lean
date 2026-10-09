import GowersSzemeredi.Proofs16PairSelectionStep

/-! Repeated genuine improvements terminate with few failed quadruple
containments, while retaining the complete list of selected Freiman maps. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_pair_frequency_selection {N d : Nat} [NeZero N] [Fact N.Prime]
    (C : Finset (Fin 4 → ZMod N)) (T : ZMod N → Finset (ZMod N)) {delta r : Real}
    (hd : 0 < delta) (hr : 0 < r) (hr4 : r < 4)
    (hT : ∀ x, (T x).card ≤ d) (hadd : ∀ q ∈ C, q 0-q 1 = q 2-q 3) :
    ∃ s : PairSelectionState N, s.Valid T delta d r ∧
      ((pairSelectionFailures C T s d r).card : Real) < delta*(N : Real)^3 ∧
      (s.maps.length : Real)*pairSelectionGain delta d r ≤ pairSelectionRank d r := by
  by_contra hnone
  have hbad (s : PairSelectionState N) (hs : s.Valid T delta d r) :
      delta*(N : Real)^3 ≤ (pairSelectionFailures C T s d r).card := by
    by_contra h
    exact hnone ⟨s,hs,lt_of_not_ge h,s.length_budget T hT hs⟩
  have hstates : ∀ n : Nat, ∃ s : PairSelectionState N, s.Valid T delta d r ∧ s.maps.length = n := by
    intro n
    induction n with
    | zero => exact ⟨emptyPairSelectionState N,emptyPairSelectionState_valid T delta d r,rfl⟩
    | succ n ih =>
      obtain ⟨s,hs,hlen⟩ := ih
      obtain ⟨s',hs',hlen',_,_⟩ := s.improve C T hd hr hr4 hT hadd hs (hbad s hs)
      exact ⟨s',hs',by omega⟩
  have hgain := pairSelectionGain_pos hd d r
  obtain ⟨n,hn⟩ := exists_nat_gt ((pairSelectionRank d r : Real)/pairSelectionGain delta d r)
  obtain ⟨s,hs,hlen⟩ := hstates n
  have hbudget := s.length_budget T hT hs
  rw [hlen] at hbudget
  have hstrict := (div_lt_iff₀ hgain).mp hn
  linarith

/-- The selected list has a modulus-independent explicit length bound. -/
theorem exists_pair_frequency_selection_count {N d : Nat} [NeZero N] [Fact N.Prime]
    (C : Finset (Fin 4 → ZMod N)) (T : ZMod N → Finset (ZMod N)) {delta r : Real}
    (hd : 0 < delta) (hr : 0 < r) (hr4 : r < 4)
    (hT : ∀ x, (T x).card ≤ d) (hadd : ∀ q ∈ C, q 0-q 1 = q 2-q 3) :
    ∃ s : PairSelectionState N, s.Valid T delta d r ∧
      ((pairSelectionFailures C T s d r).card : Real) < delta*(N : Real)^3 ∧
      s.maps.length ≤ ⌊(pairSelectionRank d r : Real)/pairSelectionGain delta d r⌋₊ := by
  obtain ⟨s,hs,hbad,hcount⟩ := exists_pair_frequency_selection C T hd hr hr4 hT hadd
  refine ⟨s,hs,hbad,?_⟩
  apply (Nat.le_floor_iff (div_nonneg (Nat.cast_nonneg _) (pairSelectionGain_pos hd d r).le)).mpr
  exact (le_div_iff₀ (pairSelectionGain_pos hd d r)).mpr hcount

end LeanProofs.GowersSzemeredi

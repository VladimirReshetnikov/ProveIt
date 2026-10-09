import GowersSzemeredi.Proofs16JointSelectionSteps

/-! Simultaneous selection terminates only when both failure families
are small. The map-count bound is independent of the modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_joint_frequency_selection {N d : Nat} [NeZero N] [Fact N.Prime]
    (C : Finset (Fin 4 → ZMod N)) (H : Finset (HigherArrangementParameter N))
    (T : ZMod N → Finset (ZMod N)) {delta r : Real}
    (hd : 0 < delta) (hr : 0 < r) (hr4 : r < 4)
    (hT : ∀ x, (T x).card ≤ d) (hadd : ∀ q ∈ C, q 0-q 1 = q 2-q 3) :
    ∃ s : PairSelectionState N, s.JointValid T delta d r ∧
      ((jointQuadrupleFailures C T s d r).card : Real) < delta*(N : Real)^3 ∧
      ((jointHigherFailures H T s d r).card : Real) < delta*(N : Real)^11 ∧
      (s.maps.length : Real)*jointSelectionGain delta d r ≤ jointSelectionRank d r := by
  by_contra hnone
  have hbad (s : PairSelectionState N) (hs : s.JointValid T delta d r) :
      delta*(N : Real)^3 ≤ (jointQuadrupleFailures C T s d r).card ∨
      delta*(N : Real)^11 ≤ (jointHigherFailures H T s d r).card := by
    by_cases hq : ((jointQuadrupleFailures C T s d r).card : Real) < delta*(N : Real)^3
    · right
      by_contra hh
      exact hnone ⟨s,hs,hq,lt_of_not_ge hh,s.joint_length_budget T hT hs⟩
    · exact Or.inl (le_of_not_gt hq)
  have hstates : ∀ n : Nat, ∃ s : PairSelectionState N, s.JointValid T delta d r ∧ s.maps.length = n := by
    intro n
    induction n with
    | zero => exact ⟨emptyPairSelectionState N,emptyPairSelectionState_joint_valid T delta d r,rfl⟩
    | succ n ih =>
      obtain ⟨s,hs,hlen⟩ := ih
      rcases hbad s hs with hq | hh
      · obtain ⟨s',hs',hlen',_,_⟩ := s.improve_joint_quadruple C T hd hr hr4 hT hadd hs hq
        exact ⟨s',hs',by omega⟩
      · obtain ⟨s',hs',hlen',_,_⟩ := s.improve_joint_higher H T hd hr hr4 hT hs hh
        exact ⟨s',hs',by omega⟩
  have hgain := jointSelectionGain_pos hd d r
  obtain ⟨n,hn⟩ := exists_nat_gt ((jointSelectionRank d r : Real)/jointSelectionGain delta d r)
  obtain ⟨s,hs,hlen⟩ := hstates n
  have hbudget := s.joint_length_budget T hT hs
  rw [hlen] at hbudget
  have hstrict := (div_lt_iff₀ hgain).mp hn
  linarith

theorem exists_joint_frequency_selection_count {N d : Nat} [NeZero N] [Fact N.Prime]
    (C : Finset (Fin 4 → ZMod N)) (H : Finset (HigherArrangementParameter N))
    (T : ZMod N → Finset (ZMod N)) {delta r : Real}
    (hd : 0 < delta) (hr : 0 < r) (hr4 : r < 4)
    (hT : ∀ x, (T x).card ≤ d) (hadd : ∀ q ∈ C, q 0-q 1 = q 2-q 3) :
    ∃ s : PairSelectionState N, s.JointValid T delta d r ∧
      ((jointQuadrupleFailures C T s d r).card : Real) < delta*(N : Real)^3 ∧
      ((jointHigherFailures H T s d r).card : Real) < delta*(N : Real)^11 ∧
      s.maps.length ≤ ⌊(jointSelectionRank d r : Real)/jointSelectionGain delta d r⌋₊ := by
  obtain ⟨s,hs,hq,hh,hcount⟩ := exists_joint_frequency_selection C H T hd hr hr4 hT hadd
  refine ⟨s,hs,hq,hh,?_⟩
  apply (Nat.le_floor_iff (div_nonneg (Nat.cast_nonneg _) (jointSelectionGain_pos hd d r).le)).mpr
  exact (le_div_iff₀ (jointSelectionGain_pos hd d r)).mpr hcount

end LeanProofs.GowersSzemeredi

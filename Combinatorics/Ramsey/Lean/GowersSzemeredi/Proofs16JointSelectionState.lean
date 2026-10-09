import GowersSzemeredi.Proofs16JointSelectionParameters

/-! Both failure tests use one state of actual maps and selected values.
Every improvement pays the smaller of the two positive density gains. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def PairSelectionState.JointValid {N : Nat} [NeZero N] (s : PairSelectionState N)
    (T : ZMod N → Finset (ZMod N)) (delta : Real) (d : Nat) (r : Real) : Prop :=
  (∀ g ∈ s.maps, g.JointControlled delta d r) ∧
  (∀ p, AddDissociated (s.frequencies p : Set (ZMod N)) ∧
    s.frequencies p ⊆ boundedFrequencySpan (fun b : ↥(T p.1 ∪ T p.2) => (b : ZMod N)) (jointSelectionCutoff d r)) ∧
  (∀ p, ∀ v ∈ s.frequencies p, ∃ g ∈ s.maps, p.1-p.2 ∈ g.domain ∧ g.toFun (p.1-p.2) = v) ∧
  (s.maps.length : Real)*jointSelectionGain delta d r*(N : Real)^2 ≤
    ∑ p : ZMod N × ZMod N, ((s.frequencies p).card : Real)

theorem emptyPairSelectionState_joint_valid {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (delta : Real) (d : Nat) (r : Real) :
    (emptyPairSelectionState N).JointValid T delta d r := by
  refine ⟨by simp [emptyPairSelectionState],?_,by simp [emptyPairSelectionState],?_⟩
  · intro p
    exact ⟨by simp [emptyPairSelectionState],Finset.empty_subset _⟩
  · simp [emptyPairSelectionState]

def jointQuadrupleFailures {N : Nat} [NeZero N]
    (C : Finset (Fin 4 → ZMod N)) (T : ZMod N → Finset (ZMod N))
    (s : PairSelectionState N) (d : Nat) (r : Real) : Finset (Fin 4 → ZMod N) :=
  C.filter fun q => ¬ bohr (pairSelectedQuadrupleFrequencies s.frequencies q) (jointSelectionRadius d r) ⊆
    bohrQuarterSum (T (q 0) ∪ T (q 1)) (T (q 2) ∪ T (q 3)) r

def jointHigherFailures {N : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N)) (T : ZMod N → Finset (ZMod N))
    (s : PairSelectionState N) (d : Nat) (r : Real) : Finset (HigherArrangementParameter N) :=
  H.filter fun p => ¬ bohr (higherSelectedPairFrequencies s.frequencies p) (jointSelectionRadius d r) ⊆
    bohrQuarterSum (higherLeftFrequencies T (higherArrangementEndpoints p))
      (higherRightFrequencies T (higherArrangementEndpoints p)) r

theorem PairSelectionState.joint_length_budget {N : Nat} [NeZero N]
    (s : PairSelectionState N) (T : ZMod N → Finset (ZMod N)) {delta r : Real} {d : Nat}
    (hT : ∀ x, (T x).card ≤ d) (hs : s.JointValid T delta d r) :
    (s.maps.length : Real)*jointSelectionGain delta d r ≤ jointSelectionRank d r := by
  have hc : (∑ p : ZMod N × ZMod N, ((s.frequencies p).card : Real)) ≤
      (N : Real)^2*jointSelectionRank d r := by
    calc _ ≤ ∑ _p : ZMod N × ZMod N, (jointSelectionRank d r : Real) := by
           apply Finset.sum_le_sum
           intro p _
           exact_mod_cast higher_pair_frequency_card_bound T s.frequencies hT
             (fun p => (hs.2.1 p).1) (fun p => (hs.2.1 p).2) p
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,ZMod.card,nsmul_eq_mul,Nat.cast_mul,pow_two]
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply le_of_mul_le_mul_right (a := (N : Real)^2) _ (by positivity)
  simpa only [mul_comm ((N : Real)^2)] using hs.2.2.2.trans hc

end LeanProofs.GowersSzemeredi

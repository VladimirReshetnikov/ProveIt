import GowersSzemeredi.Proofs16PairSelectionParameters

/-! The selection state records every chosen Freiman map and its actual
progression domain, together with the selected values at each column pair. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

structure PairFrequencyMap (N : Nat) where
  progression : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N
  shift : ZMod N
  toFun : ZMod N → ZMod N

def PairFrequencyMap.domain {N : Nat} (g : PairFrequencyMap N) : Finset (ZMod N) :=
  translatedFreimanDomain g.progression.carrier g.shift

def PairFrequencyMap.Controlled {N : Nat} (g : PairFrequencyMap N) (epsilon : Real) : Prop :=
  g.progression.rank ≤ commonDifferenceRank epsilon+1 ∧ g.progression.Proper ∧
  commonDifferenceProgressionDensity epsilon*N ≤ (g.progression.carrier.card : Real) ∧
  FreimanHom 2 g.domain g.toFun

structure PairSelectionState (N : Nat) where
  maps : List (PairFrequencyMap N)
  frequencies : (ZMod N × ZMod N) → Finset (ZMod N)

def PairSelectionState.Valid {N : Nat} [NeZero N] (s : PairSelectionState N)
    (T : ZMod N → Finset (ZMod N)) (delta : Real) (d : Nat) (r : Real) : Prop :=
  (∀ g ∈ s.maps, g.Controlled (escapingFreimanDensity delta d r)) ∧
  (∀ p, AddDissociated (s.frequencies p : Set (ZMod N)) ∧
    s.frequencies p ⊆ boundedFrequencySpan (fun b : ↥(T p.1 ∪ T p.2) => (b : ZMod N)) (pairSelectionCutoff d r)) ∧
  (∀ p, ∀ v ∈ s.frequencies p, ∃ g ∈ s.maps, p.1-p.2 ∈ g.domain ∧ g.toFun (p.1-p.2) = v) ∧
  (s.maps.length : Real)*pairSelectionGain delta d r*(N : Real)^2 ≤
    ∑ p : ZMod N × ZMod N, ((s.frequencies p).card : Real)

def emptyPairSelectionState (N : Nat) : PairSelectionState N := ⟨[],fun _ => ∅⟩

theorem emptyPairSelectionState_valid {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (delta : Real) (d : Nat) (r : Real) :
    (emptyPairSelectionState N).Valid T delta d r := by
  refine ⟨by simp [emptyPairSelectionState],?_,by simp [emptyPairSelectionState],?_⟩
  · intro p
    exact ⟨by simp [emptyPairSelectionState],Finset.empty_subset _⟩
  · simp [emptyPairSelectionState]

def pairSelectionFailures {N : Nat} [NeZero N]
    (C : Finset (Fin 4 → ZMod N)) (T : ZMod N → Finset (ZMod N))
    (s : PairSelectionState N) (d : Nat) (r : Real) : Finset (Fin 4 → ZMod N) :=
  C.filter fun q => ¬ bohr (pairSelectedQuadrupleFrequencies s.frequencies q) (pairSelectionRadius d r) ⊆
    bohrQuarterSum (T (q 0) ∪ T (q 1)) (T (q 2) ∪ T (q 3)) r

theorem PairSelectionState.length_budget {N : Nat} [NeZero N]
    (s : PairSelectionState N) (T : ZMod N → Finset (ZMod N)) {delta r : Real} {d : Nat}
    (hT : ∀ x, (T x).card ≤ d) (hs : s.Valid T delta d r) :
    (s.maps.length : Real)*pairSelectionGain delta d r ≤ pairSelectionRank d r := by
  have hc : (∑ p : ZMod N × ZMod N, ((s.frequencies p).card : Real)) ≤
      (N : Real)^2*pairSelectionRank d r := by
    calc _ ≤ ∑ _p : ZMod N × ZMod N, (pairSelectionRank d r : Real) := by
           apply Finset.sum_le_sum
           intro p _
           exact_mod_cast pair_selection_frequency_card_bound T s.frequencies r hT
             (fun p => (hs.2.1 p).1) (fun p => (hs.2.1 p).2) p
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,ZMod.card,nsmul_eq_mul,Nat.cast_mul,pow_two]
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply le_of_mul_le_mul_right (a := (N : Real)^2) _ (by positivity)
  simpa only [mul_comm ((N : Real)^2)] using hs.2.2.2.trans hc

end LeanProofs.GowersSzemeredi

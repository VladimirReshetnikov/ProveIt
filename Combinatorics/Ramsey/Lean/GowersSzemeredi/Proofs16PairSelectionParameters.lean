import GowersSzemeredi.Proofs16DensePairRankIncrement

/-! A fixed radius and rank budget work throughout the pair-frequency
selection, independently of the number of maps already selected. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def pairSelectionCutoff (d : Nat) (r : Real) : Nat := 2*bohrExtensionCutoff (2*d) r
def pairSelectionRank (d : Nat) (r : Real) : Nat := spanGeneratorBound (2*d) (pairSelectionCutoff d r)
def pairSelectionRadius (d : Nat) (r : Real) : Real :=
  1/(8*Real.pi*((pairSelectionRank d r : Real)+1))
def pairSelectionGain (delta : Real) (d : Nat) (r : Real) : Real :=
  commonDifferenceProgressionRetention (escapingFreimanDensity delta d r)

theorem pairSelectionRadius_pos (d : Nat) (r : Real) : 0 < pairSelectionRadius d r := by
  unfold pairSelectionRadius
  positivity

theorem pairSelectionGain_pos {delta : Real} (hd : 0 < delta) (d : Nat) (r : Real) :
    0 < pairSelectionGain delta d r :=
  commonDifferenceProgressionRetention_pos (escapingFreimanDensity_pos hd d r)

theorem pair_selection_frequency_card_bound {N d : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (F : (ZMod N × ZMod N) → Finset (ZMod N)) (r : Real)
    (hT : ∀ x, (T x).card ≤ d) (hF : ∀ p, AddDissociated (F p : Set (ZMod N)))
    (hFT : ∀ p, F p ⊆ boundedFrequencySpan (fun b : ↥(T p.1 ∪ T p.2) => (b : ZMod N))
      (pairSelectionCutoff d r)) (p : ZMod N × ZMod N) :
    (F p).card ≤ pairSelectionRank d r := by
  apply (subsetSum_count_rank_bound _ _ _ (dissociated_boundedSpan_count _ _ _ (hFT p) (hF p))).trans
  apply spanGeneratorBound_mono_rank
  exact (Finset.card_union_le _ _).trans (by have := hT p.1; have := hT p.2; omega)

theorem pair_selection_radius_budget {N d : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (F : (ZMod N × ZMod N) → Finset (ZMod N)) (r : Real)
    (hT : ∀ x, (T x).card ≤ d) (hF : ∀ p, AddDissociated (F p : Set (ZMod N)))
    (hFT : ∀ p, F p ⊆ boundedFrequencySpan (fun b : ↥(T p.1 ∪ T p.2) => (b : ZMod N))
      (pairSelectionCutoff d r)) (q : Fin 4 → ZMod N) :
    ((pairSelectedQuadrupleFrequencies F q).card : Real)*pairSelectionRadius d r ≤ 1/(4*Real.pi) := by
  have hc : (pairSelectedQuadrupleFrequencies F q).card ≤ 2*pairSelectionRank d r := by
    apply (Finset.card_union_le _ _).trans
    have h1 := pair_selection_frequency_card_bound T F r hT hF hFT (q 0,q 1)
    have h2 := pair_selection_frequency_card_bound T F r hT hF hFT (q 2,q 3)
    omega
  have hcR : ((pairSelectedQuadrupleFrequencies F q).card : Real) ≤ 2*(pairSelectionRank d r : Real) := by exact_mod_cast hc
  unfold pairSelectionRadius
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [Real.pi_pos]

end LeanProofs.GowersSzemeredi

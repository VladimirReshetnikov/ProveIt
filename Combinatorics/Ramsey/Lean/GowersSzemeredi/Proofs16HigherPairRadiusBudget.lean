import GowersSzemeredi.Proofs16HigherPairRankIncrement

/-! A uniform radius pays for four summands and eight selected pair
frequency sets. The bound is valid throughout independent-family growth. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherPairSelectionRadius (d C : Nat) : Real :=
  1/(128*Real.pi*((spanGeneratorBound (2*d) C : Real)+1))

theorem higherPairSelectionRadius_pos (d C : Nat) : 0 < higherPairSelectionRadius d C := by
  unfold higherPairSelectionRadius
  positivity

theorem higher_pair_frequency_card_bound {N d C : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (F : (ZMod N × ZMod N) → Finset (ZMod N))
    (hT : ∀ x, (T x).card ≤ d) (hF : ∀ e, AddDissociated (F e : Set (ZMod N)))
    (hFT : ∀ e, F e ⊆ boundedFrequencySpan (fun a : ↥(T e.1 ∪ T e.2) => (a : ZMod N)) C)
    (e : ZMod N × ZMod N) : (F e).card ≤ spanGeneratorBound (2*d) C := by
  apply (subsetSum_count_rank_bound _ _ _ (dissociated_boundedSpan_count _ _ _ (hFT e) (hF e))).trans
  apply spanGeneratorBound_mono_rank
  exact (Finset.card_union_le _ _).trans (by have := hT e.1; have := hT e.2; omega)

theorem higherSelectedPairFrequencies_card_le {N s : Nat}
    (F : (ZMod N × ZMod N) → Finset (ZMod N)) (hF : ∀ e, (F e).card ≤ s)
    (p : HigherArrangementParameter N) : (higherSelectedPairFrequencies F p).card ≤ 8*s := by
  calc (higherSelectedPairFrequencies F p).card ≤
      ∑ j : Fin 8, (F (higherArrangementEndpointPair p j)).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin 8, s := Finset.sum_le_sum (fun j _ => hF _)
    _ = 8*s := by simp

theorem higher_pair_selection_radius_budget {N d C : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (F : (ZMod N × ZMod N) → Finset (ZMod N))
    (hT : ∀ x, (T x).card ≤ d) (hF : ∀ e, AddDissociated (F e : Set (ZMod N)))
    (hFT : ∀ e, F e ⊆ boundedFrequencySpan (fun a : ↥(T e.1 ∪ T e.2) => (a : ZMod N)) C)
    (p : HigherArrangementParameter N) :
    ((higherSelectedPairFrequencies F p).card : Real)*4*higherPairSelectionRadius d C ≤ 1/(4*Real.pi) := by
  have hc := higherSelectedPairFrequencies_card_le F (higher_pair_frequency_card_bound T F hT hF hFT) p
  have hcR : ((higherSelectedPairFrequencies F p).card : Real) ≤ 8*(spanGeneratorBound (2*d) C : Real) := by
    exact_mod_cast hc
  have hmul := mul_le_mul_of_nonneg_right hcR Real.pi_pos.le
  unfold higherPairSelectionRadius
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [Real.pi_pos]

end LeanProofs.GowersSzemeredi

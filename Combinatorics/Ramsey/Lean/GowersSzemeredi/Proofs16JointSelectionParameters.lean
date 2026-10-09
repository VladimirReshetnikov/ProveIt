import GowersSzemeredi.Proofs16HigherPairRadiusBudget

/-! A common ambient cutoff and positive gain allow the quadruple and
higher-arrangement improvements to share one finite rank budget. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def jointSelectionCutoff (d : Nat) (r : Real) : Nat :=
  max (pairSelectionCutoff d r) (2*bohrExtensionCutoff (8*d) r)
def jointSelectionRank (d : Nat) (r : Real) : Nat :=
  spanGeneratorBound (2*d) (jointSelectionCutoff d r)
def jointSelectionRadius (d : Nat) (r : Real) : Real :=
  higherPairSelectionRadius d (jointSelectionCutoff d r)
def jointSelectionGain (delta : Real) (d : Nat) (r : Real) : Real :=
  min (pairSelectionGain delta d r) (higherEscapeDensity delta d r/4)

def PairFrequencyMap.JointControlled {N : Nat} (g : PairFrequencyMap N)
    (delta : Real) (d : Nat) (r : Real) : Prop :=
  g.Controlled (escapingFreimanDensity delta d r) ∨
    ∃ n < 8, g.Controlled ((higherArrangementPairDensity (higherEscapeCoordinateDensity delta d r) n)^2)

theorem jointSelectionRadius_pos (d : Nat) (r : Real) : 0 < jointSelectionRadius d r :=
  higherPairSelectionRadius_pos _ _

theorem jointSelectionGain_pos {delta : Real} (hd : 0 < delta) (d : Nat) (r : Real) :
    0 < jointSelectionGain delta d r := by
  exact lt_min (pairSelectionGain_pos hd d r) (div_pos (higherEscapeDensity_pos hd d r) (by norm_num))

theorem joint_selection_quadruple_radius_budget {N d : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (F : (ZMod N × ZMod N) → Finset (ZMod N)) (r : Real)
    (hT : ∀ x, (T x).card ≤ d) (hF : ∀ p, AddDissociated (F p : Set (ZMod N)))
    (hFT : ∀ p, F p ⊆ boundedFrequencySpan (fun b : ↥(T p.1 ∪ T p.2) => (b : ZMod N))
      (jointSelectionCutoff d r)) (q : Fin 4 → ZMod N) :
    ((pairSelectedQuadrupleFrequencies F q).card : Real)*jointSelectionRadius d r ≤ 1/(4*Real.pi) := by
  have hcard := higher_pair_frequency_card_bound T F hT hF hFT
  have hc : (pairSelectedQuadrupleFrequencies F q).card ≤ 2*jointSelectionRank d r := by
    apply (Finset.card_union_le _ _).trans
    have := hcard (q 0,q 1)
    have := hcard (q 2,q 3)
    change _ ≤ 2*spanGeneratorBound (2*d) (jointSelectionCutoff d r)
    omega
  have hcR : ((pairSelectedQuadrupleFrequencies F q).card : Real) ≤ 2*(jointSelectionRank d r : Real) := by
    exact_mod_cast hc
  have hmul := mul_le_mul_of_nonneg_right hcR Real.pi_pos.le
  change _ * (1/(128*Real.pi*((jointSelectionRank d r : Real)+1))) ≤ _
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [Real.pi_pos]

end LeanProofs.GowersSzemeredi

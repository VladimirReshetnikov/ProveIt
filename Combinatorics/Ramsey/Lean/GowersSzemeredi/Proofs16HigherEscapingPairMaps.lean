import GowersSzemeredi.Proofs16HigherFrequencyModel

/-! Actual failed higher containments yield controlled progression maps
on a common dense arrangement family, still escaping the coefficient-four
span needed to handle repeated selected frequencies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherEscapeSelectionDensity (delta : Real) (d : Nat) (r : Real) : Real :=
  delta/(2*bohrExtensionCutoff (8*d) r+1 : Nat)^(16*d)

def higherEscapeCoordinateDensity (delta : Real) (d : Nat) (r : Real) : Real :=
  higherArrangementDensity (higherEscapeSelectionDensity delta d r) 16

def higherEscapeDensity (delta : Real) (d : Nat) (r : Real) : Real :=
  higherArrangementPairDensity (higherEscapeCoordinateDensity delta d r) 8

theorem higherEscapeSelectionDensity_pos {delta : Real} (hd : 0 < delta) (d : Nat) (r : Real) :
    0 < higherEscapeSelectionDensity delta d r := by unfold higherEscapeSelectionDensity; positivity

theorem higherEscapeCoordinateDensity_pos {delta : Real} (hd : 0 < delta) (d : Nat) (r : Real) :
    0 < higherEscapeCoordinateDensity delta d r :=
  higherArrangementDensity_pos (higherEscapeSelectionDensity_pos hd d r) 16

theorem higherEscapeDensity_pos {delta : Real} (hd : 0 < delta) (d : Nat) (r : Real) :
    0 < higherEscapeDensity delta d r :=
  higherArrangementPairDensity_pos (higherEscapeCoordinateDensity_pos hd d r) 8

theorem higher_failed_containments_pair_maps {N d : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (HigherArrangementParameter N)) (T : ZMod N → Finset (ZMod N))
    (D : HigherArrangementParameter N → Finset (ZMod N)) {r sigma delta : Real}
    (hr : 0 < r) (hr4 : r < 4) (hd : 0 < delta) (hB : delta*(N : Real)^11 ≤ B.card)
    (hT : ∀ x, (T x).card ≤ d)
    (hs : ∀ p ∈ B, ((D p).card : Real)*4*sigma ≤ 1/(4*Real.pi))
    (hfail : ∀ p ∈ B, ¬ bohr (D p) sigma ⊆
      bohrQuarterSum (higherLeftFrequencies T (higherArrangementEndpoints p))
        (higherRightFrequencies T (higherArrangementEndpoints p)) r) :
    ∃ (f : Fin 16 → ZMod N → ZMod N) (theta : Fin 8 → PairFrequencyMap N)
      (Q : Finset (HigherArrangementParameter N)),
      (∀ i x, f i x ∈ boundedFrequencySpan (fun a : T x => (a : ZMod N)) (bohrExtensionCutoff (8*d) r)) ∧
      Q ⊆ B ∧
      (∀ j, ∃ n < 8, (theta j).Controlled ((higherArrangementPairDensity (higherEscapeCoordinateDensity delta d r) n)^2)) ∧
      (∀ p ∈ Q, ∀ j, higherArrangementPairDifference p j ∈ (theta j).domain ∧
        (theta j).toFun (higherArrangementPairDifference p j) = higherArrangementPairValue f p j) ∧
      (∀ p ∈ Q, HigherArrangementPairMapEquation theta p) ∧
      (∀ p ∈ Q, higherLeftPairMapValue theta p ∉ boundedFrequencySpan (fun a : D p => (a : ZMod N)) 4) ∧
      higherEscapeDensity delta d r*(N : Real)^11 ≤ Q.card := by
  let R := bohrExtensionCutoff (8*d) r
  let K := (2*R+1)^(16*d)
  obtain ⟨f,hf,hcount⟩ := exists_higher_escaping_frequency_selection B higherArrangementEndpoints T D 4 hr hr4 hT hs hfail
  let C := B.filter fun p => HigherFrequencyEquation (fun i => f i (higherArrangementEndpoints p i)) ∧
    higherLeftFrequencyValue (fun i => f i (higherArrangementEndpoints p i)) ∉
      boundedFrequencySpan (fun a : D p => (a : ZMod N)) 4
  have hcount' : B.card ≤ K*C.card := hcount
  have hK : (0 : Real) < K := by dsimp [K]; positivity
  have hC : (delta/K)*(N : Real)^11 ≤ C.card := by
    have hreal : (B.card : Real) ≤ (K : Real)*C.card := by exact_mod_cast hcount'
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hK).mpr
    simpa only [mul_comm (K : Real)] using hB.trans hreal
  have hCequation : ∀ p ∈ C, HigherArrangementEquation f p := by
    intro p hp
    exact (higherFrequencyEquation_endpoints_iff f p).mp (Finset.mem_filter.mp hp).2.1
  obtain ⟨E,theta,Q,hQC,_,_,_,hcontrol,hvalue,hequation,hQ⟩ :=
    higher_arrangements_common_pair_family f C hCequation (div_pos hd hK) hC
  refine ⟨f,theta,Q,hf,hQC.trans (Finset.filter_subset _ _),?_,hvalue,hequation,?_,?_⟩
  · simpa only [higherEscapeCoordinateDensity,higherEscapeSelectionDensity,K,R,Nat.cast_pow] using hcontrol
  · intro p hp
    rw [higherLeftPairMapValue_eq_frequency f theta p (fun j => (hvalue p hp j).2)]
    exact (Finset.mem_filter.mp (hQC hp)).2.2
  · simpa only [higherEscapeDensity,higherEscapeCoordinateDensity,higherEscapeSelectionDensity,K,R,Nat.cast_pow] using hQ

end LeanProofs.GowersSzemeredi

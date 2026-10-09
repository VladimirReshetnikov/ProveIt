import GowersSzemeredi.Proofs16DensePairFrequencyEscape
import GowersSzemeredi.Proofs16IndependentFamilyBudget

/-! A genuine failed pair-containment family gives a quantitative
simultaneous enlargement of the selected independent frequency sets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def pairSelectedQuadrupleFrequencies {N : Nat}
    (F : (ZMod N × ZMod N) → Finset (ZMod N)) (q : Fin 4 → ZMod N) : Finset (ZMod N) :=
  F (q 0,q 1) ∪ F (q 2,q 3)

theorem failed_pair_containments_increase_rank {N d : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Fin 4 → ZMod N)) (T : ZMod N → Finset (ZMod N))
    (F : (ZMod N × ZMod N) → Finset (ZMod N)) {r sigma delta : Real}
    (hr : 0 < r) (hr4 : r < 4) (hdelta : 0 < delta)
    (hB : delta*(N : Real)^3 ≤ B.card) (hadd : ∀ q ∈ B, q 0-q 1 = q 2-q 3)
    (hT : ∀ x, (T x).card ≤ d)
    (hF : ∀ p, AddDissociated (F p : Set (ZMod N)))
    (hFT : ∀ p, F p ⊆ boundedFrequencySpan (fun b : ↥(T p.1 ∪ T p.2) => (b : ZMod N))
      (2*bohrExtensionCutoff (2*d) r))
    (hs : ∀ q ∈ B, ((pairSelectedQuadrupleFrequencies F q).card : Real)*sigma ≤ 1/(4*Real.pi))
    (hfail : ∀ q ∈ B, ¬ bohr (pairSelectedQuadrupleFrequencies F q) sigma ⊆
      bohrQuarterSum (T (q 0) ∪ T (q 1)) (T (q 2) ∪ T (q 3)) r) :
    let epsilon := escapingFreimanDensity delta d r
    let R := 2*bohrExtensionCutoff (2*d) r
    ∃ (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N) (a : ZMod N)
      (theta : ZMod N → ZMod N) (E : Finset (ZMod N × ZMod N)),
      P.rank ≤ commonDifferenceRank epsilon+1 ∧ P.Proper ∧
      commonDifferenceProgressionDensity epsilon*N ≤ (P.carrier.card : Real) ∧
      FreimanHom 2 (translatedFreimanDomain P.carrier a) theta ∧
      E ⊆ B.image (fun q => (q 0,q 1)) ∧
      commonDifferenceProgressionRetention epsilon*(N : Real)^2 ≤ E.card ∧
      (∀ p ∈ E, p.1-p.2 ∈ translatedFreimanDomain P.carrier a ∧
        theta (p.1-p.2) ∉ boundedFrequencySpan (fun b : F p => (b : ZMod N)) 1) ∧
      let F' := extendIndependentFamily F E (fun p => theta (p.1-p.2))
      (∀ p, AddDissociated (F' p : Set (ZMod N)) ∧
        F' p ⊆ boundedFrequencySpan (fun b : ↥(T p.1 ∪ T p.2) => (b : ZMod N)) R ∧ F p ⊆ F' p) ∧
      (∑ p : ZMod N × ZMod N, (F' p).card) = (∑ p : ZMod N × ZMod N, (F p).card)+E.card ∧
      (∑ p : ZMod N × ZMod N, (F' p).card) ≤ N^2*spanGeneratorBound (2*d) R := by
  obtain ⟨P,a,theta,E,hPrank,hPproper,hPmass,htheta,hEB,hE,hvalue⟩ :=
    failed_containments_dense_pair_escape B T (pairSelectedQuadrupleFrequencies F) F
      hr hr4 hdelta hB hadd hT hs (fun _ _ => Finset.subset_union_left) hfail
  let K (p : ZMod N × ZMod N) := T p.1 ∪ T p.2
  let R := 2*bohrExtensionCutoff (2*d) r
  let F' := extendIndependentFamily F E (fun p => theta (p.1-p.2))
  have hnew := extendIndependentFamily_properties F K E (fun p => theta (p.1-p.2)) R hF hFT
    (fun p hp => (hvalue p hp).2)
  refine ⟨P,a,theta,E,hPrank,hPproper,hPmass,htheta,hEB,hE,
    fun p hp => ⟨(hvalue p hp).1,(hvalue p hp).2.2⟩,hnew,?_,?_⟩
  · exact extendIndependentFamily_total_card F Finset.univ E _ (Finset.subset_univ _)
      (fun p hp => (hvalue p hp).2.2)
  · have hbound := independent_family_total_card_bound F' K Finset.univ (2*d) R
      (fun p _ => (hnew p).1) (fun p _ => (hnew p).2.1)
      (fun p _ => (Finset.card_union_le _ _).trans (by have := hT p.1; have := hT p.2; omega))
    simpa only [Finset.card_univ,Fintype.card_prod,ZMod.card,pow_two] using hbound

end LeanProofs.GowersSzemeredi

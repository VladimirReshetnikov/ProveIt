import GowersSzemeredi.Proofs16HigherDensePairFrequencyEscape
import GowersSzemeredi.Proofs16IndependentFamilyBudget

/-! A dense higher-containment failure family genuinely enlarges the
selected independent pair frequencies. A flexible ambient cutoff permits
later combination with the quadruple improvement. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherSelectedPairFrequencies {N : Nat}
    (F : (ZMod N × ZMod N) → Finset (ZMod N)) (p : HigherArrangementParameter N) : Finset (ZMod N) :=
  Finset.univ.biUnion fun j : Fin 8 => F (higherArrangementEndpointPair p j)

theorem higher_failed_pair_containments_increase_rank {N d C : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (HigherArrangementParameter N)) (T : ZMod N → Finset (ZMod N))
    (F : (ZMod N × ZMod N) → Finset (ZMod N)) {r sigma delta : Real}
    (hr : 0 < r) (hr4 : r < 4) (hd : 0 < delta) (hB : delta*(N : Real)^11 ≤ B.card)
    (hT : ∀ x, (T x).card ≤ d)
    (hF : ∀ e, AddDissociated (F e : Set (ZMod N)))
    (hFT : ∀ e, F e ⊆ boundedFrequencySpan (fun a : ↥(T e.1 ∪ T e.2) => (a : ZMod N)) C)
    (hcut : 2*bohrExtensionCutoff (8*d) r ≤ C)
    (hs : ∀ p ∈ B, ((higherSelectedPairFrequencies F p).card : Real)*4*sigma ≤ 1/(4*Real.pi))
    (hfail : ∀ p ∈ B, ¬ bohr (higherSelectedPairFrequencies F p) sigma ⊆
      bohrQuarterSum (higherLeftFrequencies T (higherArrangementEndpoints p))
        (higherRightFrequencies T (higherArrangementEndpoints p)) r) :
    ∃ (j : Fin 4) (theta : PairFrequencyMap N) (E : Finset (ZMod N × ZMod N)),
      (∃ n < 8, theta.Controlled ((higherArrangementPairDensity (higherEscapeCoordinateDensity delta d r) n)^2)) ∧
      E ⊆ B.image (fun p => higherArrangementEndpointPair p (Fin.castAdd 4 j)) ∧
      (higherEscapeDensity delta d r/4)*(N : Real)^2 ≤ E.card ∧
      (∀ e ∈ E, e.1-e.2 ∈ theta.domain ∧
        theta.toFun (e.1-e.2) ∉ boundedFrequencySpan (fun a : F e => (a : ZMod N)) 1) ∧
      let F' := extendIndependentFamily F E (fun e => theta.toFun (e.1-e.2))
      (∀ e, AddDissociated (F' e : Set (ZMod N)) ∧
        F' e ⊆ boundedFrequencySpan (fun a : ↥(T e.1 ∪ T e.2) => (a : ZMod N)) C ∧ F e ⊆ F' e) ∧
      (∑ e : ZMod N × ZMod N, (F' e).card) = (∑ e : ZMod N × ZMod N, (F e).card)+E.card ∧
      (∑ e : ZMod N × ZMod N, (F' e).card) ≤ N^2*spanGeneratorBound (2*d) C := by
  obtain ⟨j,theta,E,hcontrol,hEB,hE,hvalue⟩ := higher_failed_containments_dense_pair_escape B T
    (higherSelectedPairFrequencies F) F hr hr4 hd hB hT hs
    (fun p _ j a ha => Finset.mem_biUnion.mpr ⟨Fin.castAdd 4 j,Finset.mem_univ _,ha⟩) hfail
  let K (e : ZMod N × ZMod N) := T e.1 ∪ T e.2
  let F' := extendIndependentFamily F E (fun e => theta.toFun (e.1-e.2))
  have hnew := extendIndependentFamily_properties F K E (fun e => theta.toFun (e.1-e.2)) C hF hFT
    (fun e he => ⟨boundedFrequencySpan_mono _ hcut (hvalue e he).2.1,(hvalue e he).2.2⟩)
  refine ⟨j,theta,E,hcontrol,hEB,hE,fun e he => ⟨(hvalue e he).1,(hvalue e he).2.2⟩,hnew,?_,?_⟩
  · exact extendIndependentFamily_total_card F Finset.univ E _ (Finset.subset_univ _)
      (fun e he => (hvalue e he).2.2)
  · have hbound := independent_family_total_card_bound F' K Finset.univ (2*d) C
      (fun e _ => (hnew e).1) (fun e _ => (hnew e).2.1)
      (fun e _ => (Finset.card_union_le _ _).trans (by have := hT e.1; have := hT e.2; omega))
    simpa only [Finset.card_univ,Fintype.card_prod,ZMod.card,pow_two] using hbound

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs16JointSelectedProgressionMaps
import GowersSzemeredi.Proofs16RepresentationReplacementImages

/-! The joint query property yields a large family of original four-term
representations agreeing with the selected raw column map, with endpoint
spectra only and a fixed fraction of the original radius. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def representationAgreementAlternatives {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (f : ZMod N → FourRepresentationTuple N)
    (x : ZMod N) (rho : Real) (K : Nat) : Finset (FourRepresentationTuple N) :=
  (fourDifferenceRepresentations U x).filter fun p =>
    ((bohr (representationColumnSpectrum T (f x) ∪ representationColumnSpectrum T p) rho).image
      (fun y => representationColumnMap L (f x) y-representationColumnMap L p y)).card ≤ K

/-- Every queried coordinate retains half the original representation mass
with a proved map comparison on its actual endpoint Bohr domain. -/
theorem query_original_representation_agreement {N d K : Nat} [NeZero N]
    (X U C : Finset (ZMod N)) (hUX : U ⊆ X)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    {rho kappa : Real} (hrho : 0 < rho) (hK : 0 < K)
    (hcol : ∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (L x) ∧ L x 0 = 0)
    (f : ZMod N → FourRepresentationTuple N)
    (hvalid : ∀ x ∈ C, f x ∈ fourDifferenceRepresentations U x)
    (q : Fin 4 → ZMod N) (hqC : ∀ j, q j ∈ C) (hadd : q 0-q 1+q 2-q 3 = 0)
    (hgood : flattenFourRepresentations (fun j => f (q j)) ∉ columnTupleImageExceptions U T L rho K)
    (halt : ∀ i, kappa*(N : Real)^3/2 ≤ (((fourDifferenceRepresentations U (q i)).filter
      fun p => flattenFourRepresentations (Function.update (fun j => f (q j)) i p) ∉
        columnTupleImageExceptions U T L rho K).card : Real)) :
    ∀ i, kappa*(N : Real)^3/2 ≤
      ((representationAgreementAlternatives U T L f (q i) (rho/4)
        (K*K*refinementKernelCap (8*d) (12*d) (rho/2) (rho/2))).card : Real) := by
  intro i
  have hsub : ((fourDifferenceRepresentations U (q i)).filter fun p =>
      flattenFourRepresentations (Function.update (fun j => f (q j)) i p) ∉ columnTupleImageExceptions U T L rho K) ⊆
      representationAgreementAlternatives U T L f (q i) (rho/4)
        (K*K*refinementKernelCap (8*d) (12*d) (rho/2) (rho/2)) := by
    intro p hp
    obtain ⟨hpRep,hpGood⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpRep,good_representation_replacement_image X U hUX T L hrho hK hcol
      q (fun j => f (q j)) i p (fun j => hvalid _ (hqC j)) hpRep hadd hgood hpGood⟩
  exact (halt i).trans (by exact_mod_cast Finset.card_le_card hsub)

end LeanProofs.GowersSzemeredi

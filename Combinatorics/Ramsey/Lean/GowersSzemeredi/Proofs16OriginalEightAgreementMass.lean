import GowersSzemeredi.Proofs16OriginalEightAgreementImages

/-! The actual original eight-tuple agreement predicate and its full N^7
mass. The varied anchor is recovered from the negative original block,
while endpoint image comparison follows from explicit domain removal. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def originalEightAgreementSet {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (Tpsi : Finset (ZMod N)) (psi : ZMod N → ZMod N) (a : ZMod N) (rho : Real) (K : Nat) :
    Finset (ColumnAnchorTuple N 7) :=
  (columnAnchorFibre U 7 a).filter fun t =>
    ((bohr (Tpsi ∪ columnListSpectrum T (columnAnchorList t)) rho).image
      (fun y => psi y-columnAnchorEval (fun x => L x y) (columnAnchorList t))).card ≤ K

theorem joined_source_agreement_defect {N : Nat} (L : ZMod N → ZMod N → ZMod N)
    (psi : ZMod N → ZMod N) (p q : FourRepresentationTuple N) (y : ZMod N) :
    psi y-columnAnchorEval (fun x => L x y) (columnAnchorList (joinSourceRepresentations p q)) =
      psi y-representationColumnMap L p y+representationColumnMap L q y := by
  rw [join_source_representations_eval,representationColumnMap_eq,representationColumnMap_eq]
  ring

theorem joined_source_mem_agreement {N K : Nat} [NeZero N]
    (U : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (Tpsi : Finset (ZMod N)) (psi : ZMod N → ZMod N) (rho : Real)
    {a u : ZMod N} {p q : FourRepresentationTuple N}
    (hp : p ∈ fourDifferenceRepresentations U (u+a)) (hq : q ∈ fourDifferenceRepresentations U u)
    (himage : ((bohr (Tpsi ∪ (representationColumnSpectrum T p ∪ representationColumnSpectrum T q)) rho).image
      (fun y => psi y-representationColumnMap L p y+representationColumnMap L q y)).card ≤ K) :
    joinSourceRepresentations p q ∈ originalEightAgreementSet U T L Tpsi psi a rho K := by
  refine Finset.mem_filter.mpr ⟨join_source_representations_mem_fibre U hp hq,?_⟩
  rw [bohr_union,bohr_joined_source_spectrum,←bohr_union]
  apply (image_card_le_of_eq_on_subset _ _ _ _ (fun _ h => h) ?_).trans himage
  intro y _
  exact joined_source_agreement_defect L psi p q y

/-- The full original N^7 agreement family for every valid difference-map
index, with the chosen map and original representations from one system. -/
theorem original_eight_agreement_mass {N d M J : Nat} [NeZero N]
    (X U C : Finset (ZMod N)) (hUX : U ⊆ X)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (f : ZMod N → FourRepresentationTuple N) (v : ZMod N → ZMod N)
    {rho sigma sigmaSrc lambda kappa : Real}
    (hsigma : 0 < sigma) (hsigmaR : sigma ≤ rho) (hsigmaSrc : sigma ≤ sigmaSrc)
    (hM : 0 < M) (hJ : 0 < J) (hk : 0 ≤ kappa)
    (hcol : ∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (L x) ∧ L x 0 = 0)
    (hdata : ∀ x ∈ C, (normalizedRepresentationSpectrum T f x).card ≤ 8*d ∧
      IsFreimanLinearOn (bohr (normalizedRepresentationSpectrum T f x) rho) (normalizedRepresentationMap L f x) ∧
      normalizedRepresentationMap L f x 0 = 0)
    (h8 : ∀ q : PairedColumnTuple N, (∀ i, (q i).1 ∈ C ∧ (q i).2 ∈ C) → pairedColumnIndex q=0 →
      PairedColumnImageRelation (normalizedRepresentationSpectrum T f) (normalizedRepresentationMap L f) sigma J q)
    (hsource : ∀ x ∈ C, kappa*(N : Real)^3/2 ≤ ((representationAgreementAlternatives U T L f x sigmaSrc M).card : Real))
    (a : ZMod N) (hva : v a ∈ C) (hva' : v a+a ∈ C)
    (hanchors : lambda*N ≤ ((progressionBridgeSet C a).card : Real)) :
    lambda*kappa^2/4*(N : Real)^7 ≤
      ((originalEightAgreementSet U T L (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a)
        (differenceAnchorMap (normalizedRepresentationMap L f) v a) a (sigma/2)
        (M*M*J*refinementKernelCap (24*d) (16*d) sigma sigma)).card : Real) := by
  let A := fun x => representationAgreementAlternatives U T L f x sigmaSrc M
  have hrep : ∀ x ∈ C, ∀ p ∈ A x, p ∈ fourDifferenceRepresentations U x :=
    fun _ _ _ hp => (Finset.mem_filter.mp hp).1
  have hmass := source_eight_joined_mass U C A A a hk hanchors hsource hsource hrep
  have hsub : sourceJoinedEightTuples C A A a ⊆
      originalEightAgreementSet U T L (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a)
        (differenceAnchorMap (normalizedRepresentationMap L f) v a) a (sigma/2)
        (M*M*J*refinementKernelCap (24*d) (16*d) sigma sigma) := by
    intro t ht
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨huAnchor,hRows⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hu,hua⟩ := Finset.mem_filter.mp huAnchor
    obtain ⟨hpA,hpB⟩ := Finset.mem_product.mp hRows
    have himage := original_eight_alternative_agreement_image X U C hUX T L f v hsigma hsigmaR hsigmaSrc
      hM hJ hcol hdata h8 a p.1 hva hva' hu hua p.2.1 p.2.2 hpA hpB
    exact joined_source_mem_agreement U T L _ _ (sigma/2) (hrep _ hua _ hpA) (hrep _ hu _ hpB) himage
  exact hmass.trans (by exact_mod_cast Finset.card_le_card hsub)

end LeanProofs.GowersSzemeredi

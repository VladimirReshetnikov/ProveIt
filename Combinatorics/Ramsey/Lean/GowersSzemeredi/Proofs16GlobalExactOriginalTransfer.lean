import GowersSzemeredi.Proofs16GlobalFullDomainTransfer
import GowersSzemeredi.Proofs16ExactOriginalEightAgreement

/-! Exact original-data progression transfer in the prime cyclic setting.
The same chosen progression maps are compatible and agree with the full
original N^7 tuple family on their natural domains at radius divided by
one positive uniform cap. All original witness and progression data are
retained. The additional explicit modulus bound is not yet compared with
the printed Gowers thresholds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- One positive cap for both kinds of original-data transfer defects. -/
def globalOriginalExactTransferImageCap (alpha : Real) : Nat :=
  let d := columnSpectrumCap (columnEightDensity alpha)
  let r := (1 : Real)/(8*Real.pi)
  let K := globalColumnAlmostAllTupleImageCap alpha (globalJointProgressionSourceError alpha (globalSourceAgreementCoreError alpha))
  let Jsrc := K*K*refinementKernelCap (8*d) (12*d) r r
  let M := K*K*refinementKernelCap (4*(8*d)) (2*(8*d)) r r
  let H := M*M*refinementKernelCap (4*(8*d)) (2*(8*d)) (r/2) (r/2)
  let J8 := H^4*refinementKernelCap (8*(8*d)) (4*(8*d)) (r/4) (r/4)
  let Jorig := Jsrc*Jsrc*J8*refinementKernelCap (24*d) (16*d) (r/8) (r/8)
  let JquadFull := (refinementCells (r/8))^(64*d)*J8
  let JorigFull := (refinementCells (r/16))^(24*d)*Jorig
  let Jfull := max JquadFull JorigFull
  max 1 Jfull

/-- Explicit modulus bound for exact conversion, in addition to the already
proved original-data selection bound. Final printed-budget comparison is separate. -/
def globalOriginalExactTransferModulusBound (alpha : Real) : Nat :=
  max (globalSourceAgreementCoreModulusBound alpha) (globalOriginalExactTransferImageCap alpha + 1)

theorem globalOriginalExactTransferImageCap_pos (alpha : Real) :
    0 < globalOriginalExactTransferImageCap alpha := by
  unfold globalOriginalExactTransferImageCap
  exact Nat.zero_lt_one.trans_le (le_max_left _ _)

/-- Unconditional exact transfer from the original dense bihomomorphism
and the explicit modulus bound, with the same source agreement density. -/
theorem global_original_eight_exact_transfer {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalOriginalExactTransferModulusBound alpha ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let r := (1 : Real)/(8*Real.pi)
    let kappa := globalProgressionRepresentationDensity alpha
    let delta := globalProgressionPurificationParentDensity alpha
    let K := globalColumnAlmostAllTupleImageCap alpha (globalJointProgressionSourceError alpha (globalSourceAgreementCoreError alpha))
    let Jsrc := K*K*refinementKernelCap (8*d) (12*d) r r
    let M := K*K*refinementKernelCap (4*(8*d)) (2*(8*d)) r r
    let H := M*M*refinementKernelCap (4*(8*d)) (2*(8*d)) (r/2) (r/2)
    let J8 := H^4*refinementKernelCap (8*(8*d)) (4*(8*d)) (r/4) (r/4)
    let Jorig := Jsrc*Jsrc*J8*refinementKernelCap (24*d) (16*d) (r/8) (r/8)
    let JquadFull := (refinementCells (r/8))^(64*d)*J8
    let JorigFull := (refinementCells (r/16))^(24*d)*Jorig
    let Jfull := max JquadFull JorigFull
    let Jcap := max 1 Jfull
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (U : Finset (ZMod N)) (Q P : CenteredProgression N) (f : ZMod N → FourRepresentationTuple N)
      (C : Finset (ZMod N)) (v : ZMod N → ZMod N),
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) (1/(4*Real.pi))) (L x) ∧ L x 0 = 0) ∧
      U ⊆ X ∧ globalColumnAlmostAllTupleDensity alpha*N ≤ (U.card : Real) ∧
      Q.rank ≤ globalProgressionPurificationRank alpha ∧ Q.Proper ∧ delta*N ≤ (Q.carrier.card : Real) ∧
      (∀ x ∈ Q.carrier, kappa*(N : Real)^3 ≤ ((fourDifferenceRepresentations U x).card : Real)) ∧
      (∀ x ∈ Q.carrier, f x ∈ fourDifferenceRepresentations U x) ∧
      P = centeredProgressionShrink Q 1024 ∧ P.Proper ∧ P.rank ≤ globalProgressionPurificationRank alpha ∧
      globalDifferenceProgressionDensity alpha*N ≤ (P.carrier.card : Real) ∧
      C ⊆ (centeredProgressionShrink Q 256).carrier ∧ C.Nonempty ∧
      delta*N/(2*(512 : Real)^Q.rank) ≤ (C.card : Real) ∧
      (∀ a ∈ P.carrier, v a ∈ C ∧ v a+a ∈ C ∧
        delta*N/(2*(1024 : Real)^Q.rank) ≤ ((progressionBridgeSet C a).card : Real)) ∧
      (∀ a ∈ P.carrier, (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a).card ≤ 16*d ∧
        IsFreimanLinearOn (bohr (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a) (1/(4*Real.pi)))
          (differenceAnchorMap (normalizedRepresentationMap L f) v a) ∧ differenceAnchorMap (normalizedRepresentationMap L f) v a 0=0) ∧
      (∀ y, differenceAnchorMap (normalizedRepresentationMap L f) v 0 y=0) ∧
      (∀ a b c e : ZMod N, a ∈ P.carrier → b ∈ P.carrier → c ∈ P.carrier → e ∈ P.carrier → a-b=c-e →
        ColumnPairCompatible (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v)
          (differenceAnchorMap (normalizedRepresentationMap L f) v) ((1/(4*Real.pi))/Jcap) (a,b) (c,e)) ∧
      ∀ a ∈ P.carrier, globalOriginalEightAgreementDensity alpha*(N : Real)^7 ≤
        ((originalEightExactAgreementSet U T L (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a)
          (differenceAnchorMap (normalizedRepresentationMap L f) v a) a ((1/(4*Real.pi))/Jcap)).card : Real) := by
  intro d r kappa delta K Jsrc M H J8 Jorig JquadFull JorigFull Jfull Jcap
  have hNold : globalSourceAgreementCoreModulusBound alpha ≤ N :=
    (le_max_left _ _).trans hN
  have hcap_eq : globalOriginalExactTransferImageCap alpha = Jcap := rfl
  have hKN : Jcap < N := by
    have h := (le_max_right _ _).trans hN
    change globalOriginalExactTransferImageCap alpha + 1 ≤ N at h
    rw [hcap_eq] at h
    omega
  obtain ⟨X,T,L,W,U,Q,P,f,C,v,hsys,hW,hcol,hUX,hU,hQr,hproper,hmass,hrep,hvalid,hPeq,hPproper,hPrank,hPmass,
      hC,hCne,hCmass,hv,hdiff,hzero,hquad,hagree⟩ :=
    global_original_eight_full_domain_transfer A phi ha ha1 hA hphi hNold
  let Tpsi := differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v
  let psi := differenceAnchorMap (normalizedRepresentationMap L f) v
  have hcap : Jfull ≤ Jcap := le_max_right _ _
  refine ⟨X,T,L,W,U,Q,P,f,C,v,hsys,hW,hcol,hUX,hU,hQr,hproper,hmass,hrep,hvalid,hPeq,hPproper,hPrank,hPmass,
      hC,hCne,hCmass,hv,hdiff,hzero,?_,?_⟩
  · intro a b c e haP hbP hcP heP hadd
    have hbounded : ColumnQuadImageRelation Tpsi psi (1/(4*Real.pi)) Jcap a b c e :=
      (hquad a b c e haP hbP hcP heP hadd).trans hcap
    exact column_quad_image_relation_exact P.carrier Tpsi psi (by positivity)
      (fun x hx => (hdiff x hx).2) haP hbP hcP heP hbounded hKN
  · intro a haP
    have hmasscap : globalOriginalEightAgreementDensity alpha * (N : Real)^7 ≤
        (originalEightAgreementSet U T L (Tpsi a) (psi a) a (1/(4*Real.pi)) Jcap).card :=
      (hagree a haP).trans (Nat.cast_le.mpr (Finset.card_le_card
        (original_eight_agreement_cap_mono U T L (Tpsi a) (psi a) a (1/(4*Real.pi)) hcap)))
    exact original_eight_exact_agreement_mass X U hUX T L (Tpsi a) (psi a) a
      (by positivity) (hdiff a haP).1 (hdiff a haP).2.1 (hdiff a haP).2.2 hcol hKN hmasscap

end LeanProofs.GowersSzemeredi

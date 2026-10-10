import GowersSzemeredi.Proofs16GlobalOriginalEightTransfer
import GowersSzemeredi.Proofs16OriginalEightDomainExpansion

/-! The completed transfer on the full original-radius domains. Both
quadruple compatibility and original eight-tuple agreement use one
uniform cap on the natural intersection of the maps' original domains. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem global_original_eight_full_domain_transfer {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalSourceAgreementCoreModulusBound alpha ≤ N) :
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
        ColumnQuadImageRelation (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v)
          (differenceAnchorMap (normalizedRepresentationMap L f) v) (1/(4*Real.pi)) Jfull a b c e) ∧
      ∀ a ∈ P.carrier, globalOriginalEightAgreementDensity alpha*(N : Real)^7 ≤
        ((originalEightAgreementSet U T L (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a)
          (differenceAnchorMap (normalizedRepresentationMap L f) v a) a (1/(4*Real.pi)) Jfull).card : Real) := by
  intro d r kappa delta K Jsrc M H J8 Jorig JquadFull JorigFull Jfull
  obtain ⟨X,T,L,W,U,Q,P,f,C,v,hsys,hW,hcol,hUX,hU,hQr,hproper,hmass,hrep,hvalid,hPeq,hPproper,hPrank,hPmass,
      hC,hCne,hCmass,hv,hdiff,hzero,hquad,hagree⟩ := global_original_eight_progression_transfer A phi ha ha1 hA hphi hN
  let Tpsi := differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v
  let psi := differenceAnchorMap (normalizedRepresentationMap L f) v
  have hr : 0 < r := by dsimp [r]; positivity
  have hOrigRadius : (1 : Real)/(4*Real.pi) = 2*r := by dsimp [r]; ring
  have hR8 : r/8 ≤ (1 : Real)/(4*Real.pi) := by rw [hOrigRadius]; linarith
  have hR16 : r/16 ≤ (1 : Real)/(4*Real.pi) := by rw [hOrigRadius]; linarith
  refine ⟨X,T,L,W,U,Q,P,f,C,v,hsys,hW,hcol,hUX,hU,hQr,hproper,hmass,hrep,hvalid,hPeq,hPproper,hPrank,hPmass,
    hC,hCne,hCmass,hv,hdiff,hzero,?_,?_⟩
  · intro a b c e haP hbP hcP heP hadd
    have hsmall := hquad a b c e haP hbP hcP heP hadd
    have hcard : (columnQuadSpectrum Tpsi a b c e).card ≤ 64*d := by
      have h := column_quad_spectrum_card Tpsi a b c e (hdiff a haP).1 (hdiff b hbP).1 (hdiff c hcP).1 (hdiff e heP).1
      omega
    have hf := column_quad_defect_freiman Tpsi psi (1/(4*Real.pi)) a b c e (by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact (hdiff _ haP).2.1
      · exact (hdiff _ hbP).2.1
      · exact (hdiff _ hcP).2.1
      · exact (hdiff _ heP).2.1)
    have hsmallImage : ((bohr (columnQuadSpectrum Tpsi a b c e) (r/8)).image (columnQuadDefect psi a b c e)).card ≤ J8 := by
      simpa only [ColumnQuadImageRelation,column_quad_common_domain_eq_bohr] using hsmall
    have hfull := freiman_image_expand_radius _ _ (by positivity : 0 < r/8) hR8 hcard hf hsmallImage
    change ((columnQuadCommonDomain Tpsi (1/(4*Real.pi)) a b c e).image (columnQuadDefect psi a b c e)).card ≤ Jfull
    rw [column_quad_common_domain_eq_bohr]
    exact hfull.trans (le_max_left _ _)
  · intro a haP
    have hexpand := original_eight_agreement_expand_domain X U hUX T L (Tpsi a) (psi a) a
      (by positivity : 0 < r/16) hR16 (hdiff a haP).1 (hdiff a haP).2.1
      (fun x hx => ⟨(hcol x hx).1,(hcol x hx).2.1⟩) (K := Jorig)
    have hsub : originalEightAgreementSet U T L (Tpsi a) (psi a) a (r/16) Jorig ⊆
        originalEightAgreementSet U T L (Tpsi a) (psi a) a (1/(4*Real.pi)) Jfull := by
      intro t ht
      have h := hexpand ht
      obtain ⟨hfibre,himage⟩ := Finset.mem_filter.mp h
      refine Finset.mem_filter.mpr ⟨hfibre,?_⟩
      have hcap : (refinementCells (r/16))^(16*d+8*d)*Jorig ≤ Jfull := by
        have heq : 16*d+8*d = 24*d := by ring
        rw [heq]
        exact le_max_right _ _
      exact himage.trans hcap
    exact (hagree a haP).trans (by exact_mod_cast Finset.card_le_card hsub)

end LeanProofs.GowersSzemeredi

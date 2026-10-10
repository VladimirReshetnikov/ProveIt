import GowersSzemeredi.Proofs16GlobalSourceAgreementCore
import GowersSzemeredi.Proofs16GlobalDifferenceParameters
import GowersSzemeredi.Proofs16OriginalEightTransferDensity
import GowersSzemeredi.Proofs16OriginalEightAgreementMass
import GowersSzemeredi.Proofs16PrescribedEightCore
import GowersSzemeredi.Proofs16PrescribedDifferenceAnchors

/-! Complete the original-data progression-map transfer: actual maps on a
proper progression have every quadruple compatible and an N^7 family of
original eight-tuple agreements at every index, from one selected system. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Both progression compatibility and original eight-tuple agreement,
with explicit uniform rank, mass, image caps and fixed-fraction radii. -/
theorem global_original_eight_progression_transfer {N : Nat} [NeZero N] [Fact N.Prime]
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
          (differenceAnchorMap (normalizedRepresentationMap L f) v) (r/8) J8 a b c e) ∧
      ∀ a ∈ P.carrier, globalOriginalEightAgreementDensity alpha*(N : Real)^7 ≤
        ((originalEightAgreementSet U T L (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a)
          (differenceAnchorMap (normalizedRepresentationMap L f) v a) a (r/16) Jorig).card : Real) := by
  intro d r kappa delta K Jsrc M H J8 Jorig
  obtain ⟨X,T,L,W,U,Q,f,S,hsys,hW,hcol,hUX,hU,hQr,hproper,hmass,hrep,hvalid,hdata,hindex0,hS,hmissing,hSmass,hSne,hsourceS,hquad⟩ :=
    global_source_agreement_quad_core A phi ha ha1 hA hphi hN
  have hdelta : 0 < delta := globalProgressionPurificationParentDensity_pos alpha
  have hkappa : 0 < kappa := globalProgressionRepresentationDensity_pos alpha
  have hr : 0 < r := by dsimp [r]; positivity
  have hepsilon : 0 < globalJointProgressionSourceError alpha (globalSourceAgreementCoreError alpha) := by
    unfold globalJointProgressionSourceError
    have heta := globalSourceAgreementCoreError_pos alpha
    positivity
  have hK : 0 < K := globalColumnAlmostAllTupleImageCap_pos ha ha1 hepsilon
  have hJsrc : 0 < Jsrc := Nat.mul_pos (Nat.mul_pos hK hK) (refinementKernelCap_pos _ _ hr hr)
  have hM : 0 < M := Nat.mul_pos (Nat.mul_pos hK hK) (refinementKernelCap_pos _ _ hr hr)
  have hr2 : 0 < r/2 := by positivity
  have hH : 0 < H := Nat.mul_pos (Nat.mul_pos hM hM) (refinementKernelCap_pos _ _ hr2 hr2)
  have hr4 : 0 < r/4 := by positivity
  have hJ8 : 0 < J8 := Nat.mul_pos (pow_pos hH _) (refinementKernelCap_pos _ _ hr4 hr4)
  let Tn := normalizedRepresentationSpectrum T f
  let Fn := normalizedRepresentationMap L f
  have hOrigRadius : (1 : Real)/(4*Real.pi) = 2*r := by dsimp [r]; ring
  have hTcore : ∀ x ∈ S, (Tn x).card ≤ 8*d :=
    fun x hx => (hdata x (centered_progression_shrink_subset Q 16 (hS hx))).1
  have hFcore : ∀ x ∈ S, IsFreimanLinearOn (bohr (Tn x) (r/4)) (Fn x) := by
    intro x hx
    apply column_freiman_smaller_radius _ _ ?_ (hdata x (centered_progression_shrink_subset Q 16 (hS hx))).2.1
    rw [hOrigRadius]
    linarith
  let C := S ∩ (centeredProgressionShrink Q 256).carrier
  obtain ⟨hCloss,hCmass,hCne,hEight⟩ := near_full_quad_core_eight_profile Q hproper S Tn Fn hr4 hH hdelta hmass
    hS hmissing hTcore hFcore hquad
  have hC : C ⊆ (centeredProgressionShrink Q 256).carrier := Finset.inter_subset_right
  have h8 : ∀ q : PairedColumnTuple N, (∀ i, (q i).1 ∈ C ∧ (q i).2 ∈ C) → pairedColumnIndex q=0 →
      PairedColumnImageRelation Tn Fn (r/8) J8 q := by
    simpa only [show (r/4)/2 = r/8 by ring] using hEight
  have hsourceC : ∀ x ∈ C, kappa*(N : Real)^3/2 ≤
      ((representationAgreementAlternatives U T L f x (r/2) Jsrc).card : Real) :=
    fun x hx => hsourceS x (Finset.mem_inter.mp hx).1
  have hCdata : ∀ x ∈ C, (Tn x).card ≤ 8*d ∧ IsFreimanLinearOn (bohr (Tn x) (1/(4*Real.pi))) (Fn x) ∧ Fn x 0=0 :=
    fun x hx => hdata x (centered_progression_shrink_subset Q 256 (hC hx))
  obtain ⟨v,hv⟩ := exists_prescribed_difference_anchors Q hproper C hdelta hmass hCloss
  let P := centeredProgressionShrink Q 1024
  have hPproper : P.Proper := centered_progression_shrink_proper Q hproper 1024
  have hPrank : P.rank ≤ globalProgressionPurificationRank alpha := hQr
  have hPmass : globalDifferenceProgressionDensity alpha*N ≤ (P.carrier.card : Real) := by
    have h := centered_progression_shrink_real_mass Q hproper (by decide : 0 < (1024 : Nat))
    norm_num only [Nat.cast_ofNat] at h
    have hactual : delta*N/(2048 : Real)^Q.rank ≤ (P.carrier.card : Real) :=
      (div_le_div_of_nonneg_right hmass (by positivity)).trans h
    have hu := mul_le_mul_of_nonneg_right (globalDifferenceProgressionDensity_le hQr) (Nat.cast_nonneg N)
    have heq : delta/(2048 : Real)^Q.rank*N = delta*N/(2048 : Real)^Q.rank := by ring
    rw [heq] at hu
    exact hu.trans hactual
  have hdiff : ∀ a ∈ P.carrier, (differenceAnchorSpectrum Tn v a).card ≤ 16*d ∧
      IsFreimanLinearOn (bohr (differenceAnchorSpectrum Tn v a) (1/(4*Real.pi))) (differenceAnchorMap Fn v a) ∧
      differenceAnchorMap Fn v a 0=0 := by
    intro a haP
    have h := difference_anchor_map_data C Tn Fn v (1/(4*Real.pi)) hCdata (hv a haP).1 (hv a haP).2.1
    simpa only [show 2*(8*d)=16*d by ring] using h
  have hfinalQuad := difference_progression_quad_images P.carrier C Tn Fn v (r/8)
    (fun a haP => ⟨(hv a haP).1,(hv a haP).2.1⟩) h8
  refine ⟨X,T,L,W,U,Q,P,f,C,v,hsys,hW,hcol,hUX,hU,hQr,hproper,hmass,hrep,hvalid,rfl,hPproper,hPrank,
    hPmass,hC,hCne,hCmass,hv,hdiff,difference_anchor_index_zero Fn v,hfinalQuad,?_⟩
  intro a haP
  let lambda := delta/(2*(1024 : Real)^Q.rank)
  have hanchors : lambda*N ≤ ((progressionBridgeSet C a).card : Real) := by
    have heq : lambda*N = delta*N/(2*(1024 : Real)^Q.rank) := by dsimp [lambda]; ring
    rw [heq]
    exact (hv a haP).2.2
  have hsigma : 0 < r/8 := by positivity
  have hsigmaR : r/8 ≤ (1 : Real)/(4*Real.pi) := by rw [hOrigRadius]; linarith
  have hsigmaSrc : r/8 ≤ r/2 := by linarith
  have hmass8 := original_eight_agreement_mass X U C hUX T L f v hsigma hsigmaR hsigmaSrc
    hJsrc hJ8 hkappa.le hcol hCdata h8 hsourceC a (hv a haP).1 (hv a haP).2.1 hanchors
  have heq : lambda*kappa^2/4 = delta*kappa^2/(8*(1024 : Real)^Q.rank) := by dsimp [lambda]; ring
  have hactual : delta*kappa^2/(8*(1024 : Real)^Q.rank)*(N : Real)^7 ≤
      ((originalEightAgreementSet U T L (differenceAnchorSpectrum Tn v a) (differenceAnchorMap Fn v a) a (r/16) Jorig).card : Real) := by
    simpa only [heq,show (r/8)/2 = r/16 by ring] using hmass8
  have hcoef : globalOriginalEightAgreementDensity alpha ≤ delta*kappa^2/(8*(1024 : Real)^Q.rank) :=
    globalOriginalEightAgreementDensity_le hQr
  exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans hactual

end LeanProofs.GowersSzemeredi

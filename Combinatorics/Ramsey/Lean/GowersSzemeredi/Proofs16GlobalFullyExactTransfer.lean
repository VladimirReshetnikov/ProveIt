import GowersSzemeredi.Proofs16GlobalExactOriginalTransfer
import GowersSzemeredi.Proofs16ProgressionExactEightRelations

/-! One proper original-data progression with exact quadruple and eight-tuple
compatibility, and genuine original N^7 source agreement at one positive
natural radius. The same selected system is used throughout. Thresholds and
ranks are explicit; comparison with the final printed Gowers bounds is open. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Endpoint frequency-removal cap for the exact eight-tuple extension. -/
def globalOriginalExactEightImageCap (alpha : Real) : Nat :=
  let d := 16 * columnSpectrumCap (columnEightDensity alpha)
  let sigma := ((1 : Real)/(4*Real.pi)) / globalOriginalExactTransferImageCap alpha
  refinementKernelCap (8*d) (4*d) sigma sigma

/-- Common positive natural radius for exact quadruples, eight-tuples and
original-source agreement. -/
def globalOriginalExactEightRadius (alpha : Real) : Real :=
  (((1 : Real)/(4*Real.pi)) / globalOriginalExactTransferImageCap alpha) /
    (2 * globalOriginalExactEightImageCap alpha)

/-- Explicit modulus bound retaining the original-data selection threshold. -/
def globalOriginalExactEightModulusBound (alpha : Real) : Nat :=
  max (globalOriginalExactTransferModulusBound alpha) (globalOriginalExactEightImageCap alpha + 1)

/-- Density of the proper progression on which all eight-tuples are exact. -/
def globalExactEightProgressionDensity (alpha : Real) : Real :=
  globalDifferenceProgressionDensity alpha / (512 : Real)^globalProgressionPurificationRank alpha

theorem globalOriginalExactEightImageCap_pos (alpha : Real) :
    0 < globalOriginalExactEightImageCap alpha := by
  have hK : (0 : Real) < globalOriginalExactTransferImageCap alpha := by
    exact_mod_cast globalOriginalExactTransferImageCap_pos alpha
  unfold globalOriginalExactEightImageCap
  exact refinementKernelCap_pos _ _ (by positivity) (by positivity)

theorem globalOriginalExactEightRadius_pos (alpha : Real) :
    0 < globalOriginalExactEightRadius alpha := by
  have hK : (0 : Real) < globalOriginalExactTransferImageCap alpha := by
    exact_mod_cast globalOriginalExactTransferImageCap_pos alpha
  have hJ : (0 : Real) < globalOriginalExactEightImageCap alpha := by
    exact_mod_cast globalOriginalExactEightImageCap_pos alpha
  unfold globalOriginalExactEightRadius
  positivity

/-- The original-data fully exact progression transfer. -/
theorem global_original_fully_exact_progression_transfer {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalOriginalExactEightModulusBound alpha ≤ N) :
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
    let sigma := (1/(4*Real.pi))/Jcap
    let Jeff := globalOriginalExactEightImageCap alpha
    let rExact := sigma/(2*Jeff)
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (U : Finset (ZMod N)) (Q P R : CenteredProgression N) (f : ZMod N → FourRepresentationTuple N)
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
      R = centeredProgressionShrink P 256 ∧ R.Proper ∧
      R.rank ≤ globalProgressionPurificationRank alpha ∧
      globalExactEightProgressionDensity alpha*N ≤ (R.carrier.card : Real) ∧
      C ⊆ (centeredProgressionShrink Q 256).carrier ∧ C.Nonempty ∧
      delta*N/(2*(512 : Real)^Q.rank) ≤ (C.card : Real) ∧
      (∀ a ∈ P.carrier, v a ∈ C ∧ v a+a ∈ C ∧
        delta*N/(2*(1024 : Real)^Q.rank) ≤ ((progressionBridgeSet C a).card : Real)) ∧
      (∀ a ∈ P.carrier, (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a).card ≤ 16*d ∧
        IsFreimanLinearOn (bohr (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a) (1/(4*Real.pi)))
          (differenceAnchorMap (normalizedRepresentationMap L f) v a) ∧ differenceAnchorMap (normalizedRepresentationMap L f) v a 0=0) ∧
      (∀ y, differenceAnchorMap (normalizedRepresentationMap L f) v 0 y=0) ∧
      (∀ a b c e : ZMod N, a ∈ R.carrier → b ∈ R.carrier → c ∈ R.carrier → e ∈ R.carrier → a-b=c-e →
        ColumnPairCompatible (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v)
          (differenceAnchorMap (normalizedRepresentationMap L f) v) rExact (a,b) (c,e)) ∧
      (∀ q : PairedColumnTuple N, (∀ i, (q i).1 ∈ R.carrier ∧ (q i).2 ∈ R.carrier) →
        pairedColumnIndex q = 0 → ∀ y ∈ bohr
          (pairedColumnSpectrum (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v) q) rExact,
          pairedColumnDefect (differenceAnchorMap (normalizedRepresentationMap L f) v) q y = 0) ∧
      ∀ a ∈ R.carrier, globalOriginalEightAgreementDensity alpha*(N : Real)^7 ≤
        ((originalEightExactAgreementSet U T L (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a)
          (differenceAnchorMap (normalizedRepresentationMap L f) v a) a rExact).card : Real) := by
  intro d r kappa delta K Jsrc M H J8 Jorig JquadFull JorigFull Jfull Jcap sigma Jeff rExact
  have hNold : globalOriginalExactTransferModulusBound alpha ≤ N :=
    (le_max_left _ _).trans hN
  have hJeffN : Jeff < N := by
    have h := (le_max_right _ _).trans hN
    change Jeff + 1 ≤ N at h
    omega
  have hcap_pos : 0 < Jcap := globalOriginalExactTransferImageCap_pos alpha
  have hcap_real : (1 : Real) ≤ Jcap := by exact_mod_cast hcap_pos
  have hJeffpos : 0 < Jeff := globalOriginalExactEightImageCap_pos alpha
  have hJeffreal : (1 : Real) ≤ Jeff := by exact_mod_cast hJeffpos
  have hsigma : 0 < sigma := by dsimp only [sigma]; positivity
  have hsigma_le : sigma ≤ (1 : Real)/(4*Real.pi) := by
    dsimp only [sigma]
    rw [div_le_iff₀ (by positivity)]
    have h0 : (0 : Real) ≤ 1/(4*Real.pi) := by positivity
    exact le_mul_of_one_le_right h0 hcap_real
  have hrExact_le : rExact ≤ sigma := by
    dsimp only [rExact]
    rw [div_le_iff₀ (by positivity)]
    have htwo : (1 : Real) ≤ 2 * Jeff := by linarith only [hJeffreal]
    exact le_mul_of_one_le_right hsigma.le htwo
  obtain ⟨X,T,L,W,U,Q,P,f,C,v,hsys,hW,hcol,hUX,hU,hQr,hproper,hmass,hrep,hvalid,hPeq,hPproper,hPrank,hPmass,
      hC,hCne,hCmass,hv,hdiff,hzero,hquad,hagree⟩ :=
    global_original_eight_exact_transfer A phi ha ha1 hA hphi hNold
  let Tpsi := differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v
  let psi := differenceAnchorMap (normalizedRepresentationMap L f) v
  let R := centeredProgressionShrink P 256
  have hRP : R.carrier ⊆ P.carrier := centered_progression_shrink_subset P 256
  have hRproper : R.Proper := centered_progression_shrink_proper P hPproper 256
  have hRrank : R.rank ≤ globalProgressionPurificationRank alpha := hPrank
  have hRmass : globalExactEightProgressionDensity alpha*N ≤ (R.carrier.card : Real) := by
    have hcount : (P.carrier.card : Real) ≤ (512 : Real)^P.rank * R.carrier.card := by
      exact_mod_cast centered_progression_shrink_card P hPproper (by norm_num : 0 < (256 : Nat))
    have hpower : (512 : Real)^P.rank ≤ (512 : Real)^globalProgressionPurificationRank alpha :=
      pow_le_pow_right₀ (by norm_num) hPrank
    have hmassR : globalDifferenceProgressionDensity alpha*N ≤
        (512 : Real)^globalProgressionPurificationRank alpha * R.carrier.card :=
      hPmass.trans (hcount.trans (mul_le_mul_of_nonneg_right hpower (by positivity)))
    unfold globalExactEightProgressionDensity
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    simpa only [mul_comm] using hmassR
  have hdata : ∀ x ∈ P.carrier, (Tpsi x).card ≤ 16*d ∧
      IsFreimanLinearOn (bohr (Tpsi x) sigma) (psi x) ∧ psi x 0 = 0 := by
    intro x hx
    exact ⟨(hdiff x hx).1,(hdiff x hx).2.1.mono (bohr_mono_radius _ hsigma_le),(hdiff x hx).2.2⟩
  refine ⟨X,T,L,W,U,Q,P,R,f,C,v,hsys,hW,hcol,hUX,hU,hQr,hproper,hmass,hrep,hvalid,hPeq,hPproper,hPrank,hPmass,
    rfl,hRproper,hRrank,hRmass,hC,hCne,hCmass,hv,hdiff,hzero,?_,?_,?_⟩
  · intro a b c e haR hbR hcR heR hadd
    exact (hquad a b c e (hRP haR) (hRP hbR) (hRP hcR) (hRP heR) hadd).radius_mono hrExact_le
  · intro q hq hadd
    exact progression_all_eight_exact_of_quad_compatible P Tpsi psi hsigma hdata hquad hJeffN q hq hadd
  · intro a haR
    exact (hagree a (hRP haR)).trans (Nat.cast_le.mpr (Finset.card_le_card
      (original_eight_exact_agreement_radius_mono U T L (Tpsi a) (psi a) a hrExact_le)))

end LeanProofs.GowersSzemeredi

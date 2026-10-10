import GowersSzemeredi.Proofs16QuerySourceAgreement
import GowersSzemeredi.Proofs16GlobalSelectedProgressionMaps
import GowersSzemeredi.Proofs16CenteredProgressionGeometry

/-! The original bihomomorphism supplies the full joint query property:
selected quadruple images and many original alternative representations
are controlled by the same exceptional query set. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem globalProgressionRepresentationDensity_le_one (alpha : Real) :
    globalProgressionRepresentationDensity alpha ≤ 1 := by
  have hp := globalColumnProgressionLogDensity_pos alpha
  have he : Real.exp (-globalColumnProgressionLogDensity alpha) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpow : (Real.exp (-globalColumnProgressionLogDensity alpha))^4 ≤ (1 : Real)^4 :=
    pow_le_pow_left₀ (Real.exp_pos _).le he 4
  simp only [one_pow] at hpow
  unfold globalProgressionRepresentationDensity
  linarith

def globalJointProgressionSourceError (alpha eta : Real) : Real :=
  eta*(globalProgressionRepresentationDensity alpha)^5/9

/-- The same selected original-data system controls both kinds of query
failure. Source comparisons use the raw representation maps, so no
reference-map value is mistakenly removed from an agreement statement. -/
theorem global_joint_progression_maps_with_source_queries {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha eta : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (heta : 0 < eta)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalProgressionSelectionModulusBound alpha eta ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let p := globalColumnProgressionLogDensity alpha
    let K := globalColumnAlmostAllTupleImageCap alpha (globalJointProgressionSourceError alpha eta)
    let B := fun U T L => columnTupleImageExceptions U T L (1/(4*Real.pi)) K
    let J := K*K*refinementKernelCap (8*d) (12*d) (1/(8*Real.pi)) (1/(8*Real.pi))
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (U : Finset (ZMod N)) (Q : CenteredProgression N) (f : ZMod N → FourRepresentationTuple N),
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) (1/(4*Real.pi))) (L x) ∧ L x 0 = 0) ∧
      U ⊆ X ∧ globalColumnAlmostAllTupleDensity alpha*N ≤ (U.card : Real) ∧
      (Q.rank : Real) ≤ 2+robustDifferenceBohrConstant*(p+1)^4 ∧ Q.Proper ∧
      Real.exp (-(robustDifferenceProgressionConstant*(p+1)^8))*N ≤ (Q.carrier.card : Real) ∧
      (∀ x ∈ Q.carrier, globalProgressionRepresentationDensity alpha*(N : Real)^3 ≤
        ((fourDifferenceRepresentations U x).card : Real)) ∧
      (∀ x ∈ Q.carrier, f x ∈ fourDifferenceRepresentations U x) ∧
      (∀ x ∈ Q.carrier, (normalizedRepresentationSpectrum T f x).card ≤ 8*d ∧
        IsFreimanLinearOn (bohr (normalizedRepresentationSpectrum T f x) (1/(4*Real.pi))) (normalizedRepresentationMap L f x) ∧
        normalizedRepresentationMap L f x 0 = 0) ∧
      (∀ y, normalizedRepresentationMap L f 0 y = 0) ∧
      ((progressionJointRepresentationFailures U Q.carrier f (B U T L) (globalProgressionRepresentationDensity alpha)).card : Real) ≤
        eta*(N : Real)^3 ∧
      progressionMapImageFailures Q.carrier (normalizedRepresentationSpectrum T f) (normalizedRepresentationMap L f) (1/(8*Real.pi)) K ⊆
        progressionJointRepresentationFailures U Q.carrier f (B U T L) (globalProgressionRepresentationDensity alpha) ∧
      ∀ q ∈ progressionAdditiveQuadruples Q.carrier,
        q ∉ progressionJointRepresentationFailures U Q.carrier f (B U T L) (globalProgressionRepresentationDensity alpha) →
        flattenFourRepresentations (fun j => f (q j)) ∉ B U T L ∧
        ∀ i, globalProgressionRepresentationDensity alpha*(N : Real)^3/2 ≤
          ((representationAgreementAlternatives U T L f (q i) (1/(16*Real.pi)) J).card : Real) := by
  intro d p K B J
  have hNbase : globalColumnTupleSampleModulusBound alpha 15 1 ≤ N := (le_max_left _ _).trans hN
  have hNeta : ⌈12/eta⌉₊ ≤ N := (le_max_right _ _).trans hN
  let kappa := globalProgressionRepresentationDensity alpha
  have hk : 0 < kappa := globalProgressionRepresentationDensity_pos alpha
  have hk1 : kappa ≤ 1 := globalProgressionRepresentationDensity_le_one alpha
  let epsilon := globalJointProgressionSourceError alpha eta
  have he : 0 < epsilon := by dsimp [epsilon,globalJointProgressionSourceError]; positivity
  obtain ⟨X,T,L,W,U,Gamma,y,Q,hsys,hW,hcol,hUX,hU,hGamma,hy0,hy,hzero,hbad,hQrank,hproper,hmass,hrep⟩ :=
    global_almost_all_images_with_robust_progression A phi ha ha1 he hA hphi hNbase
  obtain ⟨f,hvalid,hdata,hindex0,hjoint,hsub,hgood⟩ := exists_joint_selected_progression_maps X U Q.carrier hUX
    (cyclicCenteredGAP_zero_mem Q) T L (1/(4*Real.pi)) hcol hk hk1 hrep hbad
  have herror : (9*epsilon/(2*kappa^5))*(N : Real)^3+6*(N : Real)^2 ≤ eta*(N : Real)^3 := by
    have hceil : 12/eta ≤ (N : Real) := (Nat.le_ceil _).trans (by exact_mod_cast hNeta)
    have hraw := (div_le_iff₀ heta).mp hceil
    have heq : 9*epsilon/(2*kappa^5) = eta/2 := by
      change 9*(eta*kappa^5/9)/(2*kappa^5) = eta/2
      field_simp [ne_of_gt hk]
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_right hraw (sq_nonneg (N : Real))
    nlinarith only [hmul]
  have hqueryRadius : (1/(4*Real.pi))/2 = (1 : Real)/(8*Real.pi) := by ring
  have hsourceRadius : (1/(4*Real.pi))/4 = (1 : Real)/(16*Real.pi) := by ring
  refine ⟨X,T,L,W,U,Q,f,hsys,hW,hcol,hUX,hU,hQrank,hproper,hmass,hrep,hvalid,hdata,hindex0,
    hjoint.trans herror,?_,?_⟩
  · simpa only [hqueryRadius] using hsub
  · intro q hq hnot
    obtain ⟨hflat,halt⟩ := hgood q hq hnot
    refine ⟨hflat,?_⟩
    have hqC := (Finset.mem_filter.mp hq).2.1
    have hadd := (Finset.mem_filter.mp hq).2.2
    have hK : 0 < K := globalColumnAlmostAllTupleImageCap_pos ha ha1 he
    have hsource := query_original_representation_agreement X U Q.carrier hUX T L
      (by positivity : 0 < (1 : Real)/(4*Real.pi)) hK hcol f hvalid q hqC hadd hflat halt
    simpa only [hsourceRadius,hqueryRadius] using hsource

end LeanProofs.GowersSzemeredi

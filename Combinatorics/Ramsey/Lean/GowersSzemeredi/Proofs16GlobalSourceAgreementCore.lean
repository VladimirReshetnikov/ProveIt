import GowersSzemeredi.Proofs16GlobalJointSourceQueries
import GowersSzemeredi.Proofs16GlobalPurificationParameters
import GowersSzemeredi.Proofs16SourceAgreementQuadCore

/-! A single near-full original-data core simultaneously has every
quadruple compatible and enough original alternative representations at
every vertex. The accuracy accounts for both kinds of vertex removal. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalSourceAgreementCoreError (alpha : Real) : Real :=
  (globalProgressionPurificationParentDensity alpha)^3/(4096*(4194304 : Real)^globalProgressionPurificationRank alpha)

def globalSourceAgreementCoreModulusBound (alpha : Real) : Nat :=
  globalProgressionSelectionModulusBound alpha (globalSourceAgreementCoreError alpha)

theorem globalSourceAgreementCoreError_pos (alpha : Real) : 0 < globalSourceAgreementCoreError alpha := by
  have h := globalProgressionPurificationParentDensity_pos alpha
  unfold globalSourceAgreementCoreError
  positivity

theorem globalSourceAgreementCoreError_le {alpha : Real} {r : Nat}
    (hr : r ≤ globalProgressionPurificationRank alpha) :
    globalSourceAgreementCoreError alpha ≤
      (globalProgressionPurificationParentDensity alpha)^3/(4096*(4194304 : Real)^r) := by
  have hp := globalProgressionPurificationParentDensity_pos alpha
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 4194304) hr
  unfold globalSourceAgreementCoreError
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left hpow (by norm_num))

/-- The original bihomomorphism supplies a nonempty dense core on which
all quadruples and all pointwise original-alternative comparisons hold. -/
theorem global_source_agreement_quad_core {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalSourceAgreementCoreModulusBound alpha ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let r := (1 : Real)/(8*Real.pi)
    let K := globalColumnAlmostAllTupleImageCap alpha
      (globalJointProgressionSourceError alpha (globalSourceAgreementCoreError alpha))
    let J := K*K*refinementKernelCap (8*d) (12*d) r r
    let M := K*K*refinementKernelCap (4*(8*d)) (2*(8*d)) r r
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (U : Finset (ZMod N)) (Q : CenteredProgression N) (f : ZMod N → FourRepresentationTuple N) (S : Finset (ZMod N)),
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) (1/(4*Real.pi))) (L x) ∧ L x 0 = 0) ∧
      U ⊆ X ∧ globalColumnAlmostAllTupleDensity alpha*N ≤ (U.card : Real) ∧
      Q.rank ≤ globalProgressionPurificationRank alpha ∧ Q.Proper ∧
      globalProgressionPurificationParentDensity alpha*N ≤ (Q.carrier.card : Real) ∧
      (∀ x ∈ Q.carrier, globalProgressionRepresentationDensity alpha*(N : Real)^3 ≤
        ((fourDifferenceRepresentations U x).card : Real)) ∧
      (∀ x ∈ Q.carrier, f x ∈ fourDifferenceRepresentations U x) ∧
      (∀ x ∈ Q.carrier, (normalizedRepresentationSpectrum T f x).card ≤ 8*d ∧
        IsFreimanLinearOn (bohr (normalizedRepresentationSpectrum T f x) (1/(4*Real.pi))) (normalizedRepresentationMap L f x) ∧
        normalizedRepresentationMap L f x 0 = 0) ∧
      (∀ y, normalizedRepresentationMap L f 0 y = 0) ∧
      S ⊆ (centeredProgressionShrink Q 16).carrier ∧
      (((centeredProgressionShrink Q 16).carrier \ S).card : Real) ≤
        globalProgressionPurificationParentDensity alpha*N/(16*(1024 : Real)^Q.rank) ∧
      globalProgressionPurificationCoreDensity alpha*N ≤ (S.card : Real) ∧ S.Nonempty ∧
      (∀ x ∈ S, globalProgressionRepresentationDensity alpha*(N : Real)^3/2 ≤
        ((representationAgreementAlternatives U T L f x (r/2) J).card : Real)) ∧
      ∀ a b c e : ZMod N, a ∈ S → b ∈ S → c ∈ S → e ∈ S → a-b = c-e →
        ColumnQuadImageRelation (normalizedRepresentationSpectrum T f) (normalizedRepresentationMap L f)
          (r/4) (M*M*refinementKernelCap (4*(8*d)) (2*(8*d)) (r/2) (r/2)) a b c e := by
  intro d r K J M
  have heta := globalSourceAgreementCoreError_pos alpha
  obtain ⟨X,T,L,W,U,Q,f,hsys,hW,hcol,hUX,hU,hQrank,hproper,hmass,hrep,hvalid,hdata,hindex0,hjoint,hsub,hgood⟩ :=
    global_joint_progression_maps_with_source_queries A phi ha ha1 heta hA hphi hN
  have hQr : Q.rank ≤ globalProgressionPurificationRank alpha := by
    have hceil : 2+robustDifferenceBohrConstant*(globalColumnProgressionLogDensity alpha+1)^4 ≤
        (globalProgressionPurificationRank alpha : Real) := Nat.le_ceil _
    exact_mod_cast hQrank.trans hceil
  have hdelta := globalProgressionPurificationParentDensity_pos alpha
  have herr := globalSourceAgreementCoreError_le hQr
  have hepsilon : 0 < globalJointProgressionSourceError alpha (globalSourceAgreementCoreError alpha) := by
    unfold globalJointProgressionSourceError
    have hk := globalProgressionRepresentationDensity_pos alpha
    positivity
  have hK : 0 < K := globalColumnAlmostAllTupleImageCap_pos ha ha1 hepsilon
  have hr : 0 < r := by dsimp [r]; positivity
  have hT : ∀ x ∈ Q.carrier, (normalizedRepresentationSpectrum T f x).card ≤ 8*d := fun x hx => (hdata x hx).1
  have hF : ∀ x ∈ Q.carrier, IsFreimanLinearOn (bohr (normalizedRepresentationSpectrum T f x) r)
      (normalizedRepresentationMap L f x) := by
    intro x hx
    apply column_freiman_smaller_radius _ _ ?_ (hdata x hx).2.1
    dsimp [r]
    have hp : (0 : Real) < 1/(4*Real.pi) := by positivity
    rw [show (1 : Real)/(8*Real.pi) = (1/(4*Real.pi))/2 by ring]
    linarith
  let Bad := progressionJointRepresentationFailures U Q.carrier f
    (columnTupleImageExceptions U T L (1/(4*Real.pi)) K) (globalProgressionRepresentationDensity alpha)
  have hsource : ∀ q ∈ progressionAdditiveQuadruples Q.carrier, q ∉ Bad →
      ∀ i, globalProgressionRepresentationDensity alpha*(N : Real)^3/2 ≤
        ((representationAgreementAlternatives U T L f (q i) (r/2) J).card : Real) := by
    intro q hq hnot
    have h := (hgood q hq hnot).2
    simpa only [r,J,d,K,show (1/(8*Real.pi))/2 = (1 : Real)/(16*Real.pi) by ring] using h
  obtain ⟨S,hS,hmissing,hsourceS,hquad⟩ := exists_source_agreement_quad_core Q hproper
    (normalizedRepresentationSpectrum T f) (normalizedRepresentationMap L f) U T L f (r/2) J
    (globalProgressionRepresentationDensity alpha) Bad hr hK hdelta hmass herr hT hF hsub hjoint hsource
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hD := centered_progression_shrink_real_mass Q hproper (by decide : 0 < (16 : Nat))
  norm_num only [Nat.cast_ofNat] at hD
  have hDmass : globalProgressionPurificationParentDensity alpha*N/(32 : Real)^Q.rank ≤
      ((centeredProgressionShrink Q 16).carrier.card : Real) :=
    (div_le_div_of_nonneg_right hmass (by positivity)).trans hD
  have hpow : (32 : Real)^Q.rank ≤ (1024 : Real)^Q.rank := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hmissing32 : (((centeredProgressionShrink Q 16).carrier \ S).card : Real) ≤
      globalProgressionPurificationParentDensity alpha*N/(16*(32 : Real)^Q.rank) :=
    hmissing.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hpow (by norm_num)))
  have hpartition : (((centeredProgressionShrink Q 16).carrier \ S).card : Real)+(S.card : Real) =
      (centeredProgressionShrink Q 16).carrier.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hS
  have hbasepos : 0 < globalProgressionPurificationParentDensity alpha*N/(32 : Real)^Q.rank := by positivity
  have hSmass : globalProgressionPurificationParentDensity alpha*N/(2*(32 : Real)^Q.rank) ≤ (S.card : Real) := by
    have heq : globalProgressionPurificationParentDensity alpha*N/(16*(32 : Real)^Q.rank) =
        (globalProgressionPurificationParentDensity alpha*N/(32 : Real)^Q.rank)/16 := by ring
    have heq2 : globalProgressionPurificationParentDensity alpha*N/(2*(32 : Real)^Q.rank) =
        (globalProgressionPurificationParentDensity alpha*N/(32 : Real)^Q.rank)/2 := by ring
    rw [heq] at hmissing32
    rw [heq2]
    linarith
  have hUniform := mul_le_mul_of_nonneg_right (globalProgressionPurificationCoreDensity_le hQr) (Nat.cast_nonneg N)
  have heq : globalProgressionPurificationParentDensity alpha/(2*(32 : Real)^Q.rank)*N =
      globalProgressionPurificationParentDensity alpha*N/(2*(32 : Real)^Q.rank) := by ring
  rw [heq] at hUniform
  have hSpos : (0 : Real) < S.card := (by positivity : 0 < globalProgressionPurificationParentDensity alpha*N/(2*(32 : Real)^Q.rank)).trans_le hSmass
  exact ⟨X,T,L,W,U,Q,f,S,hsys,hW,hcol,hUX,hU,hQr,hproper,hmass,hrep,hvalid,hdata,hindex0,
    hS,hmissing,hUniform.trans hSmass,Finset.card_pos.mp (by exact_mod_cast hSpos),hsourceS,hquad⟩

end LeanProofs.GowersSzemeredi

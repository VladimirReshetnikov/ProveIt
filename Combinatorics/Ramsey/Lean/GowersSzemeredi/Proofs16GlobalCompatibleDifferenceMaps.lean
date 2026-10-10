import GowersSzemeredi.Proofs16GlobalDifferenceParameters
import GowersSzemeredi.Proofs16CompatibleDifferenceProgression

/-! Original-data compatible maps on an actual proper index progression.
The eight-term and difference-map stages retain the selected original
representations and quantitatively many anchors for every final index. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The compatibility part of the progression-map transfer, from the
original dense bihomomorphism. Eight-tuple source agreement is separate. -/
theorem global_compatible_difference_progression_maps {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalDifferenceProgressionModulusBound alpha ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let r := (1 : Real)/(8*Real.pi)
    let K := globalColumnAlmostAllTupleImageCap alpha
      (globalProgressionSelectionSourceError alpha (globalProgressionDifferenceError alpha))
    let M := K*K*refinementKernelCap (4*(8*d)) (2*(8*d)) r r
    let H := M*M*refinementKernelCap (4*(8*d)) (2*(8*d)) (r/2) (r/2)
    let J := H^4*refinementKernelCap (8*(8*d)) (4*(8*d)) (r/4) (r/4)
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (U : Finset (ZMod N)) (Q P : CenteredProgression N)
      (f : ZMod N → FourRepresentationTuple N) (C : Finset (ZMod N)) (v : ZMod N → ZMod N),
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) (1/(4*Real.pi))) (L x) ∧ L x 0 = 0) ∧
      U ⊆ X ∧ globalColumnAlmostAllTupleDensity alpha*N ≤ (U.card : Real) ∧
      Q.rank ≤ globalProgressionPurificationRank alpha ∧ Q.Proper ∧
      globalProgressionPurificationParentDensity alpha*N ≤ (Q.carrier.card : Real) ∧
      (∀ t ∈ Q.carrier, globalProgressionRepresentationDensity alpha*(N : Real)^3 ≤
        ((fourDifferenceRepresentations U t).card : Real)) ∧
      (∀ x ∈ Q.carrier, f x ∈ fourDifferenceRepresentations U x) ∧
      (∀ x ∈ Q.carrier, (normalizedRepresentationSpectrum T f x).card ≤ 8*d ∧
        IsFreimanLinearOn (bohr (normalizedRepresentationSpectrum T f x) (1/(4*Real.pi)))
          (normalizedRepresentationMap L f x) ∧ normalizedRepresentationMap L f x 0 = 0) ∧
      (∀ y, normalizedRepresentationMap L f 0 y = 0) ∧
      P = centeredProgressionShrink Q 1024 ∧ P.Proper ∧ P.rank ≤ globalProgressionPurificationRank alpha ∧
      globalDifferenceProgressionDensity alpha*N ≤ (P.carrier.card : Real) ∧
      C ⊆ (centeredProgressionShrink Q 256).carrier ∧ C.Nonempty ∧
      globalProgressionPurificationParentDensity alpha*N/(2*(512 : Real)^Q.rank) ≤ (C.card : Real) ∧
      (∀ a ∈ P.carrier, v a ∈ C ∧ v a+a ∈ C ∧
        globalProgressionPurificationParentDensity alpha*N/(2*(1024 : Real)^Q.rank) ≤
          ((progressionBridgeSet C a).card : Real)) ∧
      (∀ a ∈ P.carrier,
        (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a).card ≤ 16*d ∧
        IsFreimanLinearOn (bohr (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a) (1/(4*Real.pi)))
          (differenceAnchorMap (normalizedRepresentationMap L f) v a) ∧
        differenceAnchorMap (normalizedRepresentationMap L f) v a 0 = 0) ∧
      (∀ y, differenceAnchorMap (normalizedRepresentationMap L f) v 0 y = 0) ∧
      (∀ q : PairedColumnTuple N, (∀ i, (q i).1 ∈ C ∧ (q i).2 ∈ C) → pairedColumnIndex q = 0 →
        PairedColumnImageRelation (normalizedRepresentationSpectrum T f) (normalizedRepresentationMap L f) (r/8) J q) ∧
      ∀ a b c e : ZMod N, a ∈ P.carrier → b ∈ P.carrier → c ∈ P.carrier → e ∈ P.carrier → a-b = c-e →
        ColumnQuadImageRelation (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v)
          (differenceAnchorMap (normalizedRepresentationMap L f) v) (r/8) J a b c e := by
  intro d r K M H J
  have heta := globalProgressionDifferenceError_pos alpha
  obtain ⟨X,T,L,W,U,Q,f,hsys,hW,hcol,hUX,hU,hQrank,hproper,hmass,hrep,hvalid,hdata,hindex0,hfail⟩ :=
    global_selected_progression_maps A phi ha ha1 heta hA hphi hN
  have hQr : Q.rank ≤ globalProgressionPurificationRank alpha := by
    have hceil : 2+robustDifferenceBohrConstant*(globalColumnProgressionLogDensity alpha+1)^4 ≤
        (globalProgressionPurificationRank alpha : Real) := Nat.le_ceil _
    exact_mod_cast hQrank.trans hceil
  have hdelta := globalProgressionPurificationParentDensity_pos alpha
  have herr := globalProgressionDifferenceError_le hQr
  have hepsilon : 0 < globalProgressionSelectionSourceError alpha (globalProgressionDifferenceError alpha) := by
    unfold globalProgressionSelectionSourceError
    exact mul_pos heta (pow_pos (globalProgressionRepresentationDensity_pos alpha) _)
  have hK : 0 < K := globalColumnAlmostAllTupleImageCap_pos ha ha1 hepsilon
  have hr : 0 < r := by dsimp [r]; positivity
  have hquery : ∀ x ∈ Q.carrier, (normalizedRepresentationSpectrum T f x).card ≤ 8*d ∧
      IsFreimanLinearOn (bohr (normalizedRepresentationSpectrum T f x) r) (normalizedRepresentationMap L f x) ∧
      normalizedRepresentationMap L f x 0 = 0 := by
    intro x hx
    refine ⟨(hdata x hx).1,?_,(hdata x hx).2.2⟩
    apply column_freiman_smaller_radius _ _ ?_ (hdata x hx).2.1
    dsimp [r]
    have hp : (0 : Real) < 1/(4*Real.pi) := by positivity
    rw [show (1 : Real)/(8*Real.pi) = (1/(4*Real.pi))/2 by ring]
    linarith
  obtain ⟨C,v,hC,hCne,hCmass,hv,hdiff,hzero,h8,hquad⟩ := exists_compatible_difference_progression_maps Q hproper
    (normalizedRepresentationSpectrum T f) (normalizedRepresentationMap L f) hr hK hdelta hmass herr hquery hfail
  let P := centeredProgressionShrink Q 1024
  have hPproper : P.Proper := centered_progression_shrink_proper Q hproper 1024
  have hPrank : P.rank ≤ globalProgressionPurificationRank alpha := hQr
  have hPmass : globalDifferenceProgressionDensity alpha*N ≤ (P.carrier.card : Real) := by
    have h := centered_progression_shrink_real_mass Q hproper (by decide : 0 < (1024 : Nat))
    norm_num only [Nat.cast_ofNat] at h
    have hactual : globalProgressionPurificationParentDensity alpha*N/(2048 : Real)^Q.rank ≤ (P.carrier.card : Real) :=
      (div_le_div_of_nonneg_right hmass (by positivity)).trans h
    have huniform := mul_le_mul_of_nonneg_right (globalDifferenceProgressionDensity_le hQr) (Nat.cast_nonneg N)
    have heq : globalProgressionPurificationParentDensity alpha/(2048 : Real)^Q.rank*N =
        globalProgressionPurificationParentDensity alpha*N/(2048 : Real)^Q.rank := by ring
    rw [heq] at huniform
    exact huniform.trans hactual
  have hCdata : ∀ x ∈ C, (normalizedRepresentationSpectrum T f x).card ≤ 8*d ∧
      IsFreimanLinearOn (bohr (normalizedRepresentationSpectrum T f x) (1/(4*Real.pi)))
        (normalizedRepresentationMap L f x) ∧ normalizedRepresentationMap L f x 0 = 0 :=
    fun x hx => hdata x (centered_progression_shrink_subset Q 256 (hC hx))
  have hfinal : ∀ a ∈ P.carrier,
      (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a).card ≤ 16*d ∧
      IsFreimanLinearOn (bohr (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a) (1/(4*Real.pi)))
        (differenceAnchorMap (normalizedRepresentationMap L f) v a) ∧
      differenceAnchorMap (normalizedRepresentationMap L f) v a 0 = 0 := by
    intro a haP
    have h := difference_anchor_map_data C (normalizedRepresentationSpectrum T f)
      (normalizedRepresentationMap L f) v (1/(4*Real.pi)) hCdata (hv a haP).1 (hv a haP).2.1
    simpa only [show 2*(8*d) = 16*d by ring] using h
  exact ⟨X,T,L,W,U,Q,P,f,C,v,hsys,hW,hcol,hUX,hU,hQr,hproper,hmass,hrep,hvalid,hdata,hindex0,
    rfl,hPproper,hPrank,hPmass,hC,hCne,hCmass,hv,hfinal,hzero,h8,hquad⟩

end LeanProofs.GowersSzemeredi

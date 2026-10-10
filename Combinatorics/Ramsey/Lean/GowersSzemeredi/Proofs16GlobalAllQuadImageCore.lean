import GowersSzemeredi.Proofs16GlobalPurificationParameters

/-! A dense core of progression-indexed original-data maps respecting every
additive quadruple with an explicit endpoint image cap. All original
witnesses, representations and normalizations survive the purification. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Start from the original dense bihomomorphism, choose the uniform source
accuracy, and purify the normalized progression maps on a dense vertex core.
The rank and retained density depend only on the original density. -/
theorem global_progression_all_quad_image_core {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalProgressionPurificationModulusBound alpha ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let r := (1 : Real)/(8*Real.pi)
    let K := globalColumnAlmostAllTupleImageCap alpha
      (globalProgressionSelectionSourceError alpha (globalProgressionPurificationError alpha))
    let M := K*K*refinementKernelCap (4*(8*d)) (2*(8*d)) r r
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (U : Finset (ZMod N)) (Q : CenteredProgression N)
      (f : ZMod N → FourRepresentationTuple N) (S : Finset (ZMod N)),
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
      S ⊆ (centeredProgressionShrink Q 16).carrier ∧
      globalProgressionPurificationCoreDensity alpha*N ≤ (S.card : Real) ∧ S.Nonempty ∧
      ∀ a b c e : ZMod N, a ∈ S → b ∈ S → c ∈ S → e ∈ S → a-b = c-e →
        ColumnQuadImageRelation (normalizedRepresentationSpectrum T f) (normalizedRepresentationMap L f)
          (r/4) (M*M*refinementKernelCap (4*(8*d)) (2*(8*d)) (r/2) (r/2)) a b c e := by
  intro d r K M
  have heta := globalProgressionPurificationError_pos alpha
  obtain ⟨X,T,L,W,U,Q,f,hsys,hW,hcol,hUX,hU,hQrank,hproper,hmass,hrep,hvalid,hdata,hindex0,hfail⟩ :=
    global_selected_progression_maps A phi ha ha1 heta hA hphi hN
  have hQr : Q.rank ≤ globalProgressionPurificationRank alpha := by
    have hceil : 2+robustDifferenceBohrConstant*(globalColumnProgressionLogDensity alpha+1)^4 ≤
        (globalProgressionPurificationRank alpha : Real) := Nat.le_ceil _
    exact_mod_cast hQrank.trans hceil
  have hdelta := globalProgressionPurificationParentDensity_pos alpha
  have herr := globalProgressionPurificationError_le hQr
  have hepsilon : 0 < globalProgressionSelectionSourceError alpha (globalProgressionPurificationError alpha) := by
    unfold globalProgressionSelectionSourceError
    exact mul_pos heta (pow_pos (globalProgressionRepresentationDensity_pos alpha) _)
  have hK : 0 < K := globalColumnAlmostAllTupleImageCap_pos ha ha1 hepsilon
  have hr : 0 < r := by dsimp [r]; positivity
  have hT : ∀ x ∈ Q.carrier, (normalizedRepresentationSpectrum T f x).card ≤ 8*d :=
    fun x hx => (hdata x hx).1
  have hL : ∀ x ∈ Q.carrier, IsFreimanLinearOn (bohr (normalizedRepresentationSpectrum T f x) r)
      (normalizedRepresentationMap L f x) := by
    intro x hx
    apply column_freiman_smaller_radius _ _ ?_ (hdata x hx).2.1
    dsimp [r]
    have hp : (0 : Real) < 1/(4*Real.pi) := by positivity
    rw [show (1 : Real)/(8*Real.pi) = (1/(4*Real.pi))/2 by ring]
    linarith
  obtain ⟨S,hS,hSmass,hSne,hquad⟩ := exists_dense_progression_all_quad_image_core Q hproper
    (normalizedRepresentationSpectrum T f) (normalizedRepresentationMap L f) hr hK hdelta hmass herr hT hL hfail
  have hSuniform : globalProgressionPurificationCoreDensity alpha*N ≤ (S.card : Real) := by
    have h := mul_le_mul_of_nonneg_right (globalProgressionPurificationCoreDensity_le hQr) (Nat.cast_nonneg N)
    have heq : globalProgressionPurificationParentDensity alpha/(2*(32 : Real)^Q.rank)*N =
        globalProgressionPurificationParentDensity alpha*N/(2*(32 : Real)^Q.rank) := by ring
    rw [heq] at h
    exact h.trans hSmass
  exact ⟨X,T,L,W,U,Q,f,S,hsys,hW,hcol,hUX,hU,hQr,hproper,hmass,hrep,hvalid,hdata,
    hindex0,hS,hSuniform,hSne,hquad⟩

end LeanProofs.GowersSzemeredi

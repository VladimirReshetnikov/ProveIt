import GowersSzemeredi.Proofs16SelectedProgressionMaps

/-! Progression-indexed normalized maps with an explicit requested image
failure fraction, from the original dense bihomomorphism. The modulus
threshold accounts for repeated-index queries; no independence is assumed
for them. Original representations, local-map data and witnesses remain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem cyclicCenteredGAP_zero_mem {N : Nat} (Q : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N) :
    (0 : ZMod N) ∈ Q.carrier := by
  let z : Q.Param := fun i => ⟨Q.radius i, by omega⟩
  have hz : Q.eval z = 0 := by
    simp [OAI.Erdos3.BohrProgression.CyclicCenteredGAP.eval,
      OAI.Erdos3.BohrProgression.CyclicCenteredGAP.coeff, z]
  exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, hz⟩

def globalProgressionRepresentationDensity (alpha : Real) : Real :=
  (Real.exp (-globalColumnProgressionLogDensity alpha))^4/8

theorem globalProgressionRepresentationDensity_pos (alpha : Real) :
    0 < globalProgressionRepresentationDensity alpha := by
  unfold globalProgressionRepresentationDensity
  positivity

def globalProgressionSelectionSourceError (alpha eta : Real) : Real :=
  eta*(globalProgressionRepresentationDensity alpha)^4

def globalProgressionSelectionModulusBound (alpha eta : Real) : Nat :=
  max (globalColumnTupleSampleModulusBound alpha 15 1) (⌈12/eta⌉₊)

/-- Original-data progression maps with at most `eta*N^3` failed
quadruple image bounds, codimension at most `8d`, a common radius, and
normalization in both variables. The selection retains its original
four-term representatives at every progression point. -/
theorem global_selected_progression_maps {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha eta : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (heta : 0 < eta)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalProgressionSelectionModulusBound alpha eta ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let p := globalColumnProgressionLogDensity alpha
    let K := globalColumnAlmostAllTupleImageCap alpha (globalProgressionSelectionSourceError alpha eta)
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (U : Finset (ZMod N)) (Q : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N)
      (f : ZMod N → FourRepresentationTuple N),
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) (1/(4*Real.pi))) (L x) ∧ L x 0 = 0) ∧
      U ⊆ X ∧ globalColumnAlmostAllTupleDensity alpha*N ≤ (U.card : Real) ∧
      (Q.rank : Real) ≤ 2+robustDifferenceBohrConstant*(p+1)^4 ∧ Q.Proper ∧
      Real.exp (-(robustDifferenceProgressionConstant*(p+1)^8))*N ≤ (Q.carrier.card : Real) ∧
      (∀ t ∈ Q.carrier, globalProgressionRepresentationDensity alpha*(N : Real)^3 ≤
        ((fourDifferenceRepresentations U t).card : Real)) ∧
      (∀ x ∈ Q.carrier, f x ∈ fourDifferenceRepresentations U x) ∧
      (∀ x ∈ Q.carrier, (normalizedRepresentationSpectrum T f x).card ≤ 8*d ∧
        IsFreimanLinearOn (bohr (normalizedRepresentationSpectrum T f x) (1/(4*Real.pi)))
          (normalizedRepresentationMap L f x) ∧ normalizedRepresentationMap L f x 0 = 0) ∧
      (∀ y, normalizedRepresentationMap L f 0 y = 0) ∧
      ((progressionMapImageFailures Q.carrier (normalizedRepresentationSpectrum T f)
        (normalizedRepresentationMap L f) (1/(8*Real.pi)) K).card : Real) ≤ eta*(N : Real)^3 := by
  have hNbase : globalColumnTupleSampleModulusBound alpha 15 1 ≤ N := (le_max_left _ _).trans hN
  have hNeta : ⌈12/eta⌉₊ ≤ N := (le_max_right _ _).trans hN
  let kappa := globalProgressionRepresentationDensity alpha
  have hk : 0 < kappa := globalProgressionRepresentationDensity_pos alpha
  let epsilon := globalProgressionSelectionSourceError alpha eta
  have he : 0 < epsilon := by dsimp [epsilon, globalProgressionSelectionSourceError]; positivity
  obtain ⟨X, T, L, W, U, Gamma, y, Q, hsys, hW, hcol, hUX, hU, hGamma, hy0, hy, hzero,
      hbad, hQrank, hproper, hmass, hrep⟩ :=
    global_almost_all_images_with_robust_progression A phi ha ha1 he hA hphi hNbase
  obtain ⟨f, hvalid, hdata, hindex0, hfail⟩ := exists_selected_progression_maps X U Q.carrier hUX
    (cyclicCenteredGAP_zero_mem Q) T L (1/(4*Real.pi)) hcol hk hrep hbad
  have herror : epsilon/(2*kappa^4)*(N : Real)^3+6*(N : Real)^2 ≤ eta*(N : Real)^3 := by
    have hceil : 12/eta ≤ (N : Real) := (Nat.le_ceil _).trans (by exact_mod_cast hNeta)
    have hraw := (div_le_iff₀ heta).mp hceil
    have heq : epsilon/(2*kappa^4) = eta/2 := by
      change (eta*kappa^4)/(2*kappa^4) = eta/2
      field_simp [ne_of_gt hk]
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_right hraw (sq_nonneg (N : Real))
    nlinarith only [hmul]
  refine ⟨X, T, L, W, U, Q, f, hsys, hW, hcol, hUX, hU, hQrank, hproper, hmass, hrep,
    hvalid, hdata, hindex0, ?_⟩
  have hrho : (1/(4*Real.pi))/2 = (1 : Real)/(8*Real.pi) := by ring
  simpa only [hrho] using hfail.trans herror

end LeanProofs.GowersSzemeredi

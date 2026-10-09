import GowersSzemeredi.Proofs16CompletionParameters

/-! Uniform quantitative completion of the last three directional operators.
The modulus threshold, progression rank, density, and row radius depend
only on the prescribed initial geometry bounds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Complete dense tuple geometry with fully uniform numerical bounds. -/
theorem uniform_seven_operator_completion {N : Nat} [NeZero N] [Fact N.Prime]
    {κ : Type*} [Fintype κ] (p : CompletionParameters)
    (A : Finset (ZMod N × ZMod N)) (W F Gamma : Finset (ZMod N))
    (L : κ → ZMod N → ZMod N) (a : ZMod N)
    (hsigma : 0 < p.domainRadius) (hsigmaMax : p.domainRadius ≤ 1 / (8 * Real.pi))
    (heta : 0 < p.rowRadius) (hetaQuarter : p.rowRadius < 1 / 4) (ha : 0 < p.density)
    (hF : F.card ≤ p.fixedCap) (hGamma : Gamma.card ≤ p.domainCap) (hk : Fintype.card κ ≤ p.mapCap)
    (hN : p.modulusBound ≤ N) (hW : W ⊆ bohr Gamma (p.domainRadius / 4))
    (hL : ∀ j, IsFreimanLinearOn (bohr Gamma p.domainRadius) (L j))
    (hzero : ∀ j, L j 0 = 0) (hcard : p.density * N ≤ W.card)
    (hgeom : tupleRowGeometry A W F L a p.rowRadius) :
    ∃ (F' : Finset (ZMod N)) (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N),
      F ⊆ F' ∧ F'.card ≤ p.fixedCap + p.mapCap * p.mapCap ∧
      P.rank ≤ p.spectrumCap + 1 ∧ P.Proper ∧ 0 ∈ P.carrier ∧
      (∀ y ∈ P.carrier, -y ∈ P.carrier) ∧ P.carrier ⊆ bohr Gamma p.domainRadius ∧
      p.targetDensity * N ≤ P.carrier.card ∧
      (∀ j, FreimanHom 2 P.carrier (L j) ∧ L j 0 = 0) ∧
      ∀ y ∈ P.carrier, ∀ x ∈ bohr (F' ∪ Finset.univ.image (fun j => L j y)) p.targetRadius,
        (x, y) ∈ horDiff (verDiff (verDiff A)) := by
  letI : NeZero p.domainCells := ⟨ne_of_gt (p.domainCells_pos hsigma)⟩
  letI : NeZero p.fixedCells := ⟨ne_of_gt (p.fixedCells_pos heta)⟩
  have hH : (2 : Real)^(Fintype.card κ) ≤ p.rowRadius * p.fixedCells :=
    (pow_le_pow_right₀ (by norm_num) hk).trans (p.fixedCells_bound heta)
  have hN' := uniformCompletionModulusBound_geometry F Gamma p.density p.domainCells p.fixedCells
    p.fixedCap p.domainCap p.mapCap hF hGamma hk hN
  obtain ⟨s, hs, S, V, F', U, a', P, hGS, hS, hfull, hquarter, hVne, hV, hVcard,
    hFF', hFcard, hgeom', hU, hPrank, hPproper, hP0, hPneg, hPS, hPsize, hrows⟩ :=
    exists_adaptive_seven_operator_progression A W F Gamma L a hsigma hsigmaMax ha heta hetaQuarter
      (p.domainCells_bound hsigma) hH hN' hW hL hzero hcard hgeom
  let k := Fintype.card κ
  let m := F.card + k * k + 2 * k
  let d := max Gamma.card F.card
  let D := (adaptiveGraphState (adaptiveFillingError p.density p.domainCells p.fixedCells m)
    p.fixedCells m p.domainCells k)^[s] d
  have hsk : s ≤ p.mapCap := (hs.trans (Nat.sub_le _ _)).trans hk
  have hm : m ≤ p.frequencyCap := by
    have hsq := Nat.mul_le_mul hk hk
    dsimp only [m, k, CompletionParameters.frequencyCap]
    omega
  have hD : D ≤ p.stateBound := uniformCompletionStateBound_spec p.density p.domainCells p.fixedCells
    p.frequencyCap p.mapCap p.initialStateCap m k d s hm hk (max_le_max hGamma hF) hsk
  have hUcap : U.card ≤ p.spectrumCap := completion_spectrum_card_uniform U ha p.stateBound D hD hU
  have hFcap : F'.card ≤ p.fixedCap + p.mapCap * p.mapCap := by
    have hprod := Nat.mul_le_mul hsk hk
    omega
  have hPdomain : P.carrier ⊆ bohr Gamma p.domainRadius := hPS.trans hfull
  refine ⟨F', P, hFF', hFcap, hPrank.trans (Nat.add_le_add_right hUcap 1),
    hPproper, hP0, hPneg, hPdomain, ?_, ?_, ?_⟩
  · have hlog : 0 ≤ Real.log (1 + Real.pi) := Real.log_nonneg (by linarith [Real.pi_pos])
    have hUcast : (U.card : Real) ≤ p.spectrumCap := by exact_mod_cast hUcap
    have hU0 : (0 : Real) ≤ U.card := Nat.cast_nonneg _
    have hCap0 : (0 : Real) ≤ p.spectrumCap := Nat.cast_nonneg _
    have hexp : p.targetDensity ≤ Real.exp (-(((U.card : Real) + 1) * Real.log (1 + Real.pi) +
        10 * ((U.card : Real) + 1)^2)) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_right (add_le_add_right hUcast 1) hlog
      nlinarith
    exact (mul_le_mul_of_nonneg_right hexp (by positivity)).trans hPsize
  · intro j
    have hlin : IsFreimanLinearOn P.carrier (L j) := by
      intro x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ heq
      exact hL j x₁ x₂ x₃ x₄ (hPdomain h₁) (hPdomain h₂) (hPdomain h₃) (hPdomain h₄) heq
    exact ⟨hlin.freimanHom, hzero j⟩
  · intro y hy x hx
    apply hrows y hy x
    apply bohr_mono_radius _ _ hx
    have hp : (2 : Real)^s ≤ (2 : Real)^p.mapCap := pow_le_pow_right₀ (by norm_num) hsk
    have hdiv := div_le_div_of_nonneg_left heta.le (by positivity) hp
    exact div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right hdiv (by norm_num : (0 : Real) ≤ 4)) (by norm_num : (0 : Real) ≤ 2)

end LeanProofs.GowersSzemeredi

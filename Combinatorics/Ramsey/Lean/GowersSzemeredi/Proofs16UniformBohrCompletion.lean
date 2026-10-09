import GowersSzemeredi.Proofs16CompletionParameters
import GowersSzemeredi.Proofs16AdaptiveBohrCompletion

/-! Uniform completion over the entire robust representation Bohr set. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Complete dense tuple geometry with fully uniform numerical bounds. -/
theorem uniform_seven_operator_bohr_completion {N : Nat} [NeZero N] [Fact N.Prime]
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
    ∃ (F' U : Finset (ZMod N)),
      F ⊆ F' ∧ F'.card ≤ p.fixedCap + p.mapCap * p.mapCap ∧
      U.card ≤ p.spectrumCap ∧ bohr U (1 / (4 * Real.pi)) ⊆ bohr Gamma p.domainRadius ∧
      (∀ j, IsFreimanLinearOn (bohr U (1 / (4 * Real.pi))) (L j)) ∧
      ∀ y ∈ bohr U (1 / (4 * Real.pi)),
        ∀ x ∈ bohr (F' ∪ Finset.univ.image (fun j => L j y)) p.targetRadius,
          (x, y) ∈ horDiff (verDiff (verDiff A)) := by
  letI : NeZero p.domainCells := ⟨ne_of_gt (p.domainCells_pos hsigma)⟩
  letI : NeZero p.fixedCells := ⟨ne_of_gt (p.fixedCells_pos heta)⟩
  have hH : (2 : Real)^(Fintype.card κ) ≤ p.rowRadius * p.fixedCells :=
    (pow_le_pow_right₀ (by norm_num) hk).trans (p.fixedCells_bound heta)
  have hN' := uniformCompletionModulusBound_geometry F Gamma p.density p.domainCells p.fixedCells
    p.fixedCap p.domainCap p.mapCap hF hGamma hk hN
  obtain ⟨s, hs, S, V, F', U, a', hGS, hS, hfull, hquarter, hVne, hV, hVcard,
    hFF', hFcard, hgeom', hU, hUS, hLU, hrows⟩ :=
    exists_adaptive_seven_operator_bohr A W F Gamma L a hsigma hsigmaMax ha heta hetaQuarter
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
  refine ⟨F', U, hFF', hFcap, hUcap, hUS.trans hfull, hLU, ?_⟩
  intro y hy x hx
  apply hrows y hy x
  apply bohr_mono_radius _ _ hx
  have hp : (2 : Real)^s ≤ (2 : Real)^p.mapCap := pow_le_pow_right₀ (by norm_num) hsk
  have hdiv := div_le_div_of_nonneg_left heta.le (by positivity) hp
  exact div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right hdiv (by norm_num : (0 : Real) ≤ 4)) (by norm_num : (0 : Real) ≤ 2)

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs16DensitySevenOperator
import GowersSzemeredi.Proofs16UniformBohrCompletion
import GowersSzemeredi.Proofs16VarietyRegularStep

/-! A bilinear Bohr variety inside the full seven-operator difference set.
All parameters depend only on the original density and extraction error.
No claim of quasipolynomial bounds or map-value agreement is made here. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

namespace CompletionParameters

def varietyRadius (p : CompletionParameters) : Real :=
  min p.targetRadius (1 / (4 * Real.pi))

theorem varietyRadius_pos (p : CompletionParameters) (h : 0 < p.rowRadius) :
    0 < p.varietyRadius := lt_min (p.targetRadius_pos h) (by positivity)

end CompletionParameters

/-- Uniform geometric containment in all seven directional operators. -/
theorem global_seven_operator_bilinear_bohr {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) {alpha epsilon : Real}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (he : 0 < epsilon)
    (hebeta : epsilon < (alpha / (2 - alpha))^4)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hN : globalSevenModulusBound alpha epsilon ≤ N) :
    let p := globalSevenParameters alpha epsilon
    ∃ (k : Nat) (F U : Finset (ZMod N)) (L : Fin k → ZMod N → ZMod N),
      k ≤ p.mapCap ∧ F.card ≤ p.fixedCap + p.mapCap * p.mapCap ∧
      U.card ≤ p.spectrumCap ∧ 0 < p.varietyRadius ∧
      (∀ j, IsFreimanLinearOn (bohr U p.varietyRadius) (L j) ∧ L j 0 = 0) ∧
      bilinearBohrVariety F U L p.varietyRadius ⊆
        horDiff (verDiff (verDiff (horDiff (verDiff (horDiff (horDiff A)))))) := by
  let p := globalSevenParameters alpha epsilon
  have hNinitial : 8 / epsilon ≤ (N : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _).trans hN)
  have hNcompletion : p.modulusBound ≤ N := (le_max_right _ _).trans hN
  have hinit : 0 < p.domainRadius ∧ p.domainRadius ≤ 1 / (8 * Real.pi) ∧
      0 < p.rowRadius ∧ p.rowRadius < 1 / 4 ∧ 0 < p.density ∧
      ∃ (k : Nat) (T F W : Finset (ZMod N)) (a : ZMod N) (L : Fin k → ZMod N → ZMod N),
        k ≤ p.mapCap ∧ T.card ≤ p.domainCap ∧ F.card ≤ p.fixedCap ∧ W.Nonempty ∧
        W ⊆ bohr T (p.domainRadius / 4) ∧ p.density * N ≤ W.card ∧
        (∀ j, IsFreimanLinearOn (bohr T p.domainRadius) (L j) ∧ L j 0 = 0) ∧
        tupleRowGeometry (horDiff (verDiff (horDiff (horDiff A)))) W F L a p.rowRadius := by
    simpa only [p, globalSevenParameters] using global_uniform_tuple_geometry A ha ha1 he hebeta hA hNinitial
  obtain ⟨hsigma, hsigmaMax, heta, hetaQuarter, ha0, k, T, F, W, a, L,
    hk, hT, hF, hWne, hW, hcard, hL, hgeom⟩ := hinit
  obtain ⟨F', U, hFF', hFcap, hUcap, hUdomain, hLU, hrows⟩ :=
    uniform_seven_operator_bohr_completion p (horDiff (verDiff (horDiff (horDiff A)))) W F T L a
      hsigma hsigmaMax heta hetaQuarter ha0 hF hT (by simpa only [Fintype.card_fin] using hk)
      hNcompletion hW (fun j => (hL j).1) (fun j => (hL j).2) hcard hgeom
  have hsub : bohr U p.varietyRadius ⊆ bohr U (1 / (4 * Real.pi)) :=
    bohr_mono_radius U (min_le_right _ _)
  refine ⟨k, F', U, L, hk, hFcap, hUcap, p.varietyRadius_pos heta, ?_, ?_⟩
  · intro j
    refine ⟨?_, (hL j).2⟩
    intro y₁ y₂ y₃ y₄ h₁ h₂ h₃ h₄ heq
    exact hLU j y₁ y₂ y₃ y₄ (hsub h₁) (hsub h₂) (hsub h₃) (hsub h₄) heq
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hxy := Finset.mem_product.mp hz'.1
    apply hrows z.2 (hsub hxy.2) z.1
    apply bohr_mono_radius _ (min_le_left _ _)
    rw [bohr_union]
    exact Finset.mem_inter.mpr ⟨hxy.1, hz'.2⟩

/-- A density-only bilinear Bohr variety theorem for sufficiently large primes. -/
theorem density_seven_operator_bilinear_bohr {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) {alpha : Real}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hN : densitySevenModulusBound alpha ≤ N) :
    let p := densitySevenParameters alpha
    ∃ (k : Nat) (F U : Finset (ZMod N)) (L : Fin k → ZMod N → ZMod N),
      k ≤ p.mapCap ∧ F.card ≤ p.fixedCap + p.mapCap * p.mapCap ∧
      U.card ≤ p.spectrumCap ∧ 0 < p.varietyRadius ∧
      (∀ j, IsFreimanLinearOn (bohr U p.varietyRadius) (L j) ∧ L j 0 = 0) ∧
      bilinearBohrVariety F U L p.varietyRadius ⊆
        horDiff (verDiff (verDiff (horDiff (verDiff (horDiff (horDiff A)))))) := by
  have hbeta : 0 < alpha / (2 - alpha) := div_pos ha (by linarith)
  exact global_seven_operator_bilinear_bohr A ha ha1 (by positivity)
    (by have h := pow_pos hbeta 4; linarith) hA hN

end LeanProofs.GowersSzemeredi

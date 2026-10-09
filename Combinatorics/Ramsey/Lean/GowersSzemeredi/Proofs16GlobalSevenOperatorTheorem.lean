import GowersSzemeredi.Proofs16UniformSevenOperatorCompletion
import GowersSzemeredi.Proofs16GlobalUniformTupleGeometry

/-! Global density yields a proper progression of filled Bohr rows in the
seven-directional-difference set. All thresholds and geometric bounds
are explicit functions of the original density parameters. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalSevenParameters (alpha epsilon : Real) : CompletionParameters :=
  let delta := alpha / 2
  let beta := alpha / (2 - alpha)
  let r := ⌈16 * delta ^ (-(2 : Real))⌉₊
  let R := directionalQuarterSpanCutoff r 64 (1 / (8 * Real.pi))
  let ell := spanGeneratorBound r R
  let K := denseRowAlphabetBound delta
  let kappa := corollary20Kappa (epsilon / 2) K
  let sigma := kappa / (32 * Real.pi)
  let width := Real.log (1 + sigma⁻¹)
  let eta := (1 / (16 * (max 1 ell : Nat) : Real)) / 2
  let M := ⌈(K : Real) / kappa⌉₊
  let t := ⌈(2 * ell : Nat) * (16 * kappa ^ (-(2 : Real)))⌉₊
  { fixedCap := 4 * ell, domainCap := t, mapCap := 2 * ell,
    domainRadius := sigma, rowRadius := eta,
    density := progressionGeometryDensity beta epsilon width ell M t }

def globalSevenModulusBound (alpha epsilon : Real) : Nat :=
  max ⌈8 / epsilon⌉₊ (globalSevenParameters alpha epsilon).modulusBound

/-- Global seven-operator completion with no graph, representation, or
structure oracle. This bound is not identified with the printed constants. -/
theorem global_seven_operator_proper_progression {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) {alpha epsilon : Real}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (he : 0 < epsilon)
    (hebeta : epsilon < (alpha / (2 - alpha))^4)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hN : globalSevenModulusBound alpha epsilon ≤ N) :
    let p := globalSevenParameters alpha epsilon
    ∃ (k : Nat) (F : Finset (ZMod N)) (L : Fin k → ZMod N → ZMod N)
      (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N),
      k ≤ p.mapCap ∧ F.card ≤ p.fixedCap + p.mapCap * p.mapCap ∧
      P.rank ≤ p.spectrumCap + 1 ∧ P.Proper ∧ 0 ∈ P.carrier ∧
      (∀ y ∈ P.carrier, -y ∈ P.carrier) ∧
      0 < p.targetRadius ∧ 0 < p.targetDensity ∧ p.targetDensity * N ≤ P.carrier.card ∧
      (∀ j, FreimanHom 2 P.carrier (L j) ∧ L j 0 = 0) ∧
      ∀ y ∈ P.carrier, ∀ x ∈ bohr (F ∪ Finset.univ.image (fun j => L j y)) p.targetRadius,
        (x, y) ∈ horDiff (verDiff (verDiff (horDiff (verDiff (horDiff (horDiff A)))))) := by
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
  obtain ⟨F', P, hFF', hFcap, hPrank, hPproper, hP0, hPneg, hPdomain, hPsize, hLP, hrows⟩ :=
    uniform_seven_operator_completion p (horDiff (verDiff (horDiff (horDiff A)))) W F T L a
      hsigma hsigmaMax heta hetaQuarter ha0 hF hT (by simpa only [Fintype.card_fin] using hk)
      hNcompletion hW (fun j => (hL j).1) (fun j => (hL j).2) hcard hgeom
  exact ⟨k, F', L, P, hk, hFcap, hPrank, hPproper, hP0, hPneg,
    p.targetRadius_pos heta, p.targetDensity_pos, hPsize, hLP, hrows⟩

end LeanProofs.GowersSzemeredi

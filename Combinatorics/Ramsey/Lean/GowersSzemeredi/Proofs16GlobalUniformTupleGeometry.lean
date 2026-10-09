import GowersSzemeredi.Proofs16UniformGeometryDensity
import GowersSzemeredi.Proofs16TuplePatternBridge
import GowersSzemeredi.Proofs16PatternBohrDegrees

/-! Uniform initial tuple geometry from global density. Only selected maps
are retained; rank and density bounds depend on the input parameters. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Global density supplies the initial data for adaptive completion with
uniform frequency caps and a strictly positive ambient-density bound. -/
theorem global_uniform_tuple_geometry {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) {alpha epsilon : Real}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (he : 0 < epsilon)
    (hebeta : epsilon < (alpha / (2 - alpha))^4)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hN : 8 / epsilon ≤ (N : Real)) :
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
    let a0 := progressionGeometryDensity beta epsilon width ell M t
    0 < sigma ∧ sigma ≤ 1 / (8 * Real.pi) ∧ 0 < eta ∧ eta < 1 / 4 ∧ 0 < a0 ∧
    ∃ (k : Nat) (T F W : Finset (ZMod N)) (a : ZMod N) (L : Fin k → ZMod N → ZMod N),
      k ≤ 2 * ell ∧ T.card ≤ t ∧ F.card ≤ 4 * ell ∧ W.Nonempty ∧
      W ⊆ bohr T (sigma / 4) ∧ a0 * N ≤ W.card ∧
      (∀ j, IsFreimanLinearOn (bohr T sigma) (L j) ∧ L j 0 = 0) ∧
      tupleRowGeometry (horDiff (verDiff (horDiff (horDiff A)))) W F L a eta := by
  dsimp only
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
  have hK : 0 < K := denseRowAlphabetBound_pos delta
  have hKR : (0 : Real) < K := by exact_mod_cast hK
  have hkappa : 0 < kappa := by dsimp [kappa, corollary20Kappa]; positivity
  have hden : 0 < 2 - alpha := by linarith
  have hb : 0 ≤ beta := (div_pos ha hden).le
  have hb1 : beta ≤ 1 := (div_le_one hden).mpr (by linarith)
  have he1 : epsilon ≤ 1 := hebeta.le.trans (by simpa using pow_le_pow_left₀ hb hb1 4)
  have hk1 : kappa ≤ 1 := corollary20Kappa_le_one (by positivity) (by linarith) K hK
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  have hsmax : sigma ≤ 1 / (8 * Real.pi) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [Real.pi_pos]
  have hmax : (1 : Real) ≤ (max 1 ell : Nat) := by exact_mod_cast (le_max_left 1 ell)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetaMax : eta < 1 / 4 := by
    have h : 1 / (16 * (max 1 ell : Nat) : Real) ≤ 1 / 16 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    dsimp only [eta]; linarith
  have ha0 := progressionGeometryDensity_pos (width := width) hebeta ell M t
  refine ⟨hsigma, hsmax, heta, hetaMax, ha0, ?_⟩
  obtain ⟨m, J, T, F, P, a, W, psi, hm, hJ, hT, hF, hPR, hPproper, hP0, hPneg,
    hPB, hWne, hWP, hWrel, hWambient, hfour, hpsi, hvar, hgeom⟩ :=
    global_proper_progression_geometry A ha ha1 he hebeta hA hN
  have hmM : m ≤ M := by
    have h : (m : Real) ≤ K / kappa := (le_div_iff₀ hkappa).mpr (by linarith)
    exact Nat.cast_le.mp (h.trans (Nat.le_ceil _))
  have hTt : T.card ≤ t := Nat.cast_le.mp (hT.trans (Nat.le_ceil _))
  let I := J 0 ∪ J 2
  let L0 : ↥I → ZMod N → ZMod N := fun i => psi i
  let L := tuplePatternMaps L0
  have hI : I.card ≤ 2 * ell := (Finset.card_union_le _ _).trans (by have h0 : (J 0).card ≤ ell := hJ 0; have h2 : (J 2).card ≤ ell := hJ 2; omega)
  have himage (y : ZMod N) : Finset.univ.image (fun j => L j y) = varyingPatternFrequencies psi J y := by
    have h := tuplePattern_frequencies L0 y
    simp only [varyingPatternFrequencies, tuplePatternIndices, Finset.union_self] at h
    exact h.trans (patternVaryingTuple_image psi J y)
  refine ⟨Fintype.card ↥I, T, F, W, a, L, ?_, hTt, hF, hWne, hWP.trans hPB, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hI
  · have hw : 0 ≤ width := Real.log_nonneg (by have : 0 ≤ sigma⁻¹ := inv_nonneg.mpr hsigma.le; linarith)
    have hbound := progressionGeometryDensity_antitone_caps hebeta.le hw ell M t m T.card hmM hTt
    exact (mul_le_mul_of_nonneg_right hbound (by positivity)).trans hWambient
  · intro j
    have hmem := ((Fintype.equivFin ↥I).symm j).property
    have h := hpsi _ hmem
    exact ⟨h.1.isFreimanLinearOn (by decide), h.2.1⟩
  · intro y hy d hd hv
    rw [himage y] at hv
    exact hgeom y hy d hd hv

end LeanProofs.GowersSzemeredi

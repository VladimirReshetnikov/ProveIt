import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairUniformFactors

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators
open RationalFilteredNilmanifold

private theorem bounds_of_sum {ci fa lt ml B : ℝ}
    (hci : 0 ≤ ci) (hfa : 0 ≤ fa) (hlt : 0 ≤ lt) (hml : 0 ≤ ml)
    (hciFast : ci ≤ fa) (hsum : fa + lt + ml ≤ B) :
    ci ∈ Set.Icc 0 B ∧ fa ∈ Set.Icc 0 B ∧
      lt ∈ Set.Icc 0 B ∧ ml ∈ Set.Icc 0 B := by
  exact ⟨⟨hci, by linarith⟩, ⟨hfa, by linarith⟩,
    ⟨hlt, by linarith⟩, ⟨hml, by linarith⟩⟩

theorem exists_candidateFrontFactor_power_budget
    (s Cdesc Cgeometry Cpair Cbasis K T Cmark : ℕ) :
    ∃ Ctotal : ℕ, 2 ≤ Ctotal ∧ ∀ p : ℝ, 0 ≤ p →
    let vertical := verticalDecompositionBudget (3 * p + 1)
    let factor := 2 * p + vertical + 2
    let desc := (p + 2) ^ Cdesc
    let geom := p + desc + 2
    let pairGeo := (geom + 2) ^ 2
    let jointGeo := (geom + 3) ^ 2
    let adapted := (jointGeo + 2) ^ Cgeometry
    let bnd := adapted + (pairGeo + 3) ^ 5 + pairGeo + jointGeo + geom + factor + 2
    let localCost := allocatedFrozenTaggedPairBudget s Cpair Cbasis pairGeo factor
    let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
    let fullCost := jointCost + (jointCost + K) ^ K
    let common := (fullCost + 2) ^ T + (((fullCost + 2) ^ 2 + 2) ^ 63 + 1) + fullCost + 1
    let projected := common + adapted + 1
    let markHeight := quotientInducedMarkHeightBudget geom
    let markInput := jointGeo + markHeight + adapted + 2
    let markBudget := (markInput + 2) ^ Cmark
    let commonInput := p + geom + pairGeo + jointGeo + jointGeo ^ 2 + adapted + bnd + factor +
      common + projected + (projected + 2) ^ 4 + markHeight + markInput + markBudget + 2
    let fast := allocatedCandidateCommonFastBudget s commonInput
    let longThreshold := (factor + 2 + Cpair) ^ Cpair + 7 * factor + 22 +
      (fullCost + 2) ^ T + p + 1
    let massLog := p + vertical * p + ((common + 2) ^ 5 + common)
    commonInput ∈ Set.Icc 0 ((p + 2) ^ Ctotal) ∧
      fast ∈ Set.Icc 0 ((p + 2) ^ Ctotal) ∧
      longThreshold ∈ Set.Icc 0 ((p + 2) ^ Ctotal) ∧
      massLog ∈ Set.Icc 0 ((p + 2) ^ Ctotal) := by
  let X : Polynomial ℕ := Polynomial.X
  let ca := (3 * X + 1 + 3) ^ 9 + 2 * (3 * X + 1) + 2
  let vertical := 2 * ca * (2 * ca + 2) ^ 4 +
    ((2 * ca + 2) ^ 4 + ca + (3 * X + 1 + 3) ^ 5 + 2) ^ 4
  let factor := 2 * X + vertical + 2
  let desc := (X + 2) ^ Cdesc
  let geom := X + desc + 2
  let pairGeo := (geom + 2) ^ 2
  let jointGeo := (geom + 3) ^ 2
  let adapted := (jointGeo + 2) ^ Cgeometry
  let bnd := adapted + (pairGeo + 3) ^ 5 + pairGeo + jointGeo + geom + factor + 2
  let transfer := pairGeo + factor + ((factor + 2 + Polynomial.C Cpair) ^ Cpair +
    Polynomial.C s * (9 * factor + 23))
  let localCost := (((pairGeo + 3) ^ 5 + transfer + 1 + 2) ^ 4 + transfer + 1 +
    Polynomial.C Cbasis) ^ Cbasis
  let jointCost := bnd + localCost + (bnd + 3) ^ 4 + 1
  let fullCost := jointCost + (jointCost + Polynomial.C K) ^ K
  let common := (fullCost + 2) ^ T + (((fullCost + 2) ^ 2 + 2) ^ 63 + 1) + fullCost + 1
  let projected := common + adapted + 1
  let markHeight := (geom + (geom + 3) ^ 7 + 3) ^ 4
  let markInput := jointGeo + markHeight + adapted + 2
  let markBudget := (markInput + 2) ^ Cmark
  let commonInput := X + geom + pairGeo + jointGeo + jointGeo ^ 2 + adapted + bnd + factor +
    common + projected + (projected + 2) ^ 4 + markHeight + markInput + markBudget + 2
  let sec := (commonInput + 2) ^ 4 + 1
  let fast := (sec + 2) ^ 47 + 1 +
    (2 * (commonInput + Polynomial.C (s + 3)) ^ (s + 3) +
      ((commonInput + Polynomial.C (s + 3)) ^ (s + 3)) ^ 2 + commonInput)
  let longThreshold := (factor + 2 + Polynomial.C Cpair) ^ Cpair + 7 * factor + 22 +
    (fullCost + 2) ^ T + X + 1
  let massLog := X + vertical * X + ((common + 2) ^ 5 + common)
  obtain ⟨Ctotal, hCtotal, htotal⟩ :=
    exists_natPolynomial_fixed_power_budget (fast + longThreshold + massLog)
  refine ⟨Ctotal, hCtotal, ?_⟩
  intro p hp v f d g pg jg a b l j full c proj mh mi mb ci fa lt ml
  have hv : 0 ≤ v := verticalDecompositionBudget_nonneg (by positivity)
  have hf : 0 ≤ f := by dsimp only [f]; positivity
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hg : 0 ≤ g := by dsimp only [g]; positivity
  have hpg : 0 ≤ pg := by dsimp only [pg]; positivity
  have hjg : 0 ≤ jg := by dsimp only [jg]; positivity
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hl : 0 ≤ l := by
    dsimp only [l, allocatedFrozenTaggedPairBudget, fixedAdaptedSymbolTransferInput]
    positivity
  have hj : 0 ≤ j := by dsimp only [j, allocatedFrozenTaggedFamilyInputBudget]; positivity
  have hfull : 0 ≤ full := by dsimp only [full]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hproj : 0 ≤ proj := by dsimp only [proj]; positivity
  have hmh : 0 ≤ mh := by dsimp only [mh, quotientInducedMarkHeightBudget]; positivity
  have hmi : 0 ≤ mi := by dsimp only [mi]; positivity
  have hmb : 0 ≤ mb := by dsimp only [mb]; positivity
  have hci : 0 ≤ ci := by dsimp only [ci]; positivity
  have hciFast : ci ≤ fa := (allocatedCandidateCommonFastBudget_bounds s hci).2.2
  have hfa : 0 ≤ fa := hci.trans hciFast
  have hlt : 0 ≤ lt := by dsimp only [lt]; positivity
  have hml : 0 ≤ ml := by dsimp only [ml]; positivity
  have eval_ca : ca.eval₂ (Nat.castRingHom ℝ) p = centralActionBudget (3 * p + 1) := by
    simp only [ca, X, centralActionBudget, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Polynomial.eval₂_one]
  have eval_vertical : vertical.eval₂ (Nat.castRingHom ℝ) p = v := by
    simp only [vertical, v, verticalDecompositionBudget, X, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Polynomial.eval₂_one, eval_ca]
  have eval_factor : factor.eval₂ (Nat.castRingHom ℝ) p = f := by
    simp only [factor, f, X, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
      Polynomial.eval₂_ofNat, eval_vertical]
  have eval_desc : desc.eval₂ (Nat.castRingHom ℝ) p = d := by
    simp only [desc, d, X, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_ofNat]
  have eval_geom : geom.eval₂ (Nat.castRingHom ℝ) p = g := by
    simp only [geom, g, X, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_ofNat, eval_desc]
  have eval_pairGeo : pairGeo.eval₂ (Nat.castRingHom ℝ) p = pg := by
    simp only [pairGeo, pg, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_ofNat, eval_geom]
  have eval_jointGeo : jointGeo.eval₂ (Nat.castRingHom ℝ) p = jg := by
    simp only [jointGeo, jg, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_ofNat, eval_geom]
  have eval_adapted : adapted.eval₂ (Nat.castRingHom ℝ) p = a := by
    simp only [adapted, a, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_ofNat, eval_jointGeo]
  have eval_bnd : bnd.eval₂ (Nat.castRingHom ℝ) p = b := by
    simp only [bnd, b, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_ofNat, eval_factor,
      eval_geom, eval_pairGeo, eval_jointGeo, eval_adapted]
  have eval_transfer : transfer.eval₂ (Nat.castRingHom ℝ) p = pg + f + ((f + 2 + Cpair) ^ Cpair + (s : ℝ) * (9 * f + 23)) := by
    simp only [transfer, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_ofNat, Nat.coe_castRingHom, eval_factor, eval_pairGeo]
  have eval_localCost : localCost.eval₂ (Nat.castRingHom ℝ) p = l := by
    simp only [localCost, l, allocatedFrozenTaggedPairBudget, fixedAdaptedSymbolTransferInput,
      Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_ofNat,
      Polynomial.eval₂_one, Nat.coe_castRingHom, eval_pairGeo, eval_transfer]
  have eval_jointCost : jointCost.eval₂ (Nat.castRingHom ℝ) p = j := by
    simp only [jointCost, j, allocatedFrozenTaggedFamilyInputBudget, Polynomial.eval₂_add,
      Polynomial.eval₂_pow, Polynomial.eval₂_ofNat, Polynomial.eval₂_one, eval_bnd, eval_localCost]
  have eval_fullCost : fullCost.eval₂ (Nat.castRingHom ℝ) p = full := by
    simp only [fullCost, full, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_C,
      Nat.coe_castRingHom, eval_jointCost]
  have eval_common : common.eval₂ (Nat.castRingHom ℝ) p = c := by
    simp only [common, c, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_ofNat,
      Polynomial.eval₂_one, eval_fullCost]
  have eval_projected : projected.eval₂ (Nat.castRingHom ℝ) p = proj := by
    simp only [projected, proj, Polynomial.eval₂_add, Polynomial.eval₂_one, eval_adapted, eval_common]
  have eval_markHeight : markHeight.eval₂ (Nat.castRingHom ℝ) p = mh := by
    simp only [markHeight, mh, quotientInducedMarkHeightBudget, Polynomial.eval₂_add,
      Polynomial.eval₂_pow, Polynomial.eval₂_ofNat, eval_geom]
  have eval_markInput : markInput.eval₂ (Nat.castRingHom ℝ) p = mi := by
    simp only [markInput, mi, Polynomial.eval₂_add, Polynomial.eval₂_ofNat, eval_jointGeo, eval_adapted,
      eval_markHeight]
  have eval_markBudget : markBudget.eval₂ (Nat.castRingHom ℝ) p = mb := by
    simp only [markBudget, mb, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_ofNat,
      eval_markInput]
  have eval_commonInput : commonInput.eval₂ (Nat.castRingHom ℝ) p = ci := by
    simp only [commonInput, ci, X, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_ofNat, eval_factor, eval_geom, eval_pairGeo, eval_jointGeo, eval_adapted,
      eval_bnd, eval_common, eval_projected, eval_markHeight, eval_markInput, eval_markBudget]
  have eval_sec : sec.eval₂ (Nat.castRingHom ℝ) p = allocatedCandidateCommonFastSectionInput ci := by
    simp only [sec, allocatedCandidateCommonFastSectionInput, Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_ofNat, Polynomial.eval₂_one, eval_commonInput]
  have eval_fast : fast.eval₂ (Nat.castRingHom ℝ) p = fa := by
    simp only [fast, fa, allocatedCandidateCommonFastBudget, allocatedCandidateCommonFastGeometryLog,
      NilpotentLieFiltration.pointwiseFastSectionInput, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_ofNat, Polynomial.eval₂_one,
      Nat.coe_castRingHom, Nat.cast_add, Nat.cast_ofNat, eval_commonInput, eval_sec]
  have eval_longThreshold : longThreshold.eval₂ (Nat.castRingHom ℝ) p = lt := by
    simp only [longThreshold, lt, X, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_ofNat, Polynomial.eval₂_one,
      Nat.coe_castRingHom, eval_factor, eval_fullCost]
  have eval_massLog : massLog.eval₂ (Nat.castRingHom ℝ) p = ml := by
    simp only [massLog, ml, X, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_ofNat, eval_vertical, eval_common]
  have hsum : fa + lt + ml ≤ (p + 2) ^ Ctotal := by
    simpa only [Polynomial.eval₂_add, eval_fast, eval_longThreshold, eval_massLog]
      using htotal p hp
  exact bounds_of_sum hci hfa hlt hml hciFast hsum

end Erdos3.VectorPolynomial

end

end OAI

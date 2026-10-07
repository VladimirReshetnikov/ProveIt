import OAI.Combinatorics.Progressions.Polynomial.CandidateFrontFactorPolynomialBudget
import OAI.Combinatorics.Progressions.Probability.CandidateFrontFactorMassBlockBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open RationalFilteredNilmanifold

attribute [local irreducible] candidateFrontFactorScalarConclusion

theorem candidateFrontFactor_actual_bounds
    (s Cgeometry Cpair Cbasis K T Cmark : ℕ)
    {p factor geom actualFactor actualGeometry cost nVariables : ℝ}
    (hp : 0 ≤ p) (hfactor : 0 ≤ actualFactor) (hgeometry : 0 ≤ actualGeometry)
    (hfactor_le : actualFactor ≤ factor) (hgeometry_le : actualGeometry ≤ geom)
    (hcost : cost ≤ p) (hvariables0 : 0 ≤ nVariables) (hvariables : nVariables ≤ p) :
    let pairGeo : ℝ := (geom + 2) ^ 2
    let jointGeo : ℝ := (geom + 3) ^ 2
    let adapted : ℝ := (jointGeo + 2) ^ Cgeometry
    let bnd : ℝ := adapted + (pairGeo + 3) ^ 5 + pairGeo + jointGeo + geom + factor + 2
    let localCost : ℝ := allocatedFrozenTaggedPairBudget s Cpair Cbasis pairGeo factor
    let jointCost : ℝ := allocatedFrozenTaggedFamilyInputBudget bnd localCost
    let fullCost : ℝ := jointCost + (jointCost + K) ^ K
    let common : ℝ := (fullCost + 2) ^ T + (((fullCost + 2) ^ 2 + 2) ^ 63 + 1) + fullCost + 1
    let projected : ℝ := common + adapted + 1
    let markHeight : ℝ := quotientInducedMarkHeightBudget geom
    let markInput : ℝ := jointGeo + markHeight + adapted + 2
    let markBudget : ℝ := (markInput + 2) ^ Cmark
    let commonInput : ℝ := p + geom + pairGeo + jointGeo + jointGeo ^ 2 + adapted + bnd + factor +
      common + projected + (projected + 2) ^ 4 + markHeight + markInput + markBudget + 2
    let fast : ℝ := allocatedCandidateCommonFastBudget s commonInput
    let longThreshold : ℝ := (factor + 2 + Cpair) ^ Cpair + 7 * factor + 22 +
      (fullCost + 2) ^ T + p + 1
    let aPairGeo : ℝ := (actualGeometry + 2) ^ 2
    let aJointGeo : ℝ := (actualGeometry + 3) ^ 2
    let aAdapted : ℝ := (aJointGeo + 2) ^ Cgeometry
    let aBnd : ℝ := aAdapted + (aPairGeo + 3) ^ 5 + aPairGeo + aJointGeo +
      actualGeometry + actualFactor + 2
    let aLocalCost : ℝ := allocatedFrozenTaggedPairBudget s Cpair Cbasis aPairGeo actualFactor
    let aJointCost : ℝ := allocatedFrozenTaggedFamilyInputBudget aBnd aLocalCost
    let aFullCost : ℝ := aJointCost + (aJointCost + K) ^ K
    let aCommon : ℝ := (aFullCost + 2) ^ T + (((aFullCost + 2) ^ 2 + 2) ^ 63 + 1) + aFullCost + 1
    let aProjected : ℝ := max aCommon 0 + aAdapted + 1
    let aMarkInput : ℝ := nativeOptionFixedSourceQuotientMarkInput actualGeometry
    let aMarkBudget : ℝ := (aMarkInput + 2) ^ Cmark
    let terminal : ℝ := (aProjected + 2) ^ 4 + aMarkInput + aMarkBudget + aJointGeo + nVariables + 2
    let initialShort : ℝ := max ((actualFactor + 2 + Cpair) ^ Cpair + 7 * actualFactor + 22)
      ((aFullCost + 2) ^ T)
    candidateFrontFactorScalarConclusion s p actualGeometry cost terminal commonInput fast
      longThreshold aProjected aCommon aMarkInput common aAdapted aMarkBudget aJointGeo initialShort := by
  intro pg jg ad bd lc jc fc co pr mh mi mb ci fa lt
    apg ajg aad abd alc ajc afc aco apr ami amb terminal initialShort
  unfold candidateFrontFactorScalarConclusion
  have hf : 0 ≤ factor := hfactor.trans hfactor_le
  have hg : 0 ≤ geom := hgeometry.trans hgeometry_le
  have hpg0 : 0 ≤ pg := by dsimp only [pg]; positivity
  have hjg0 : 0 ≤ jg := by dsimp only [jg]; positivity
  have had0 : 0 ≤ ad := by dsimp only [ad]; positivity
  have hbpow0 : 0 ≤ (pg + 3) ^ 5 := by positivity
  have hbd0 : 0 ≤ bd := by dsimp only [bd]; positivity
  have hlc0 : 0 ≤ lc := by
    dsimp only [lc, allocatedFrozenTaggedPairBudget, fixedAdaptedSymbolTransferInput]
    positivity
  have hjc0 : 0 ≤ jc := by dsimp only [jc, allocatedFrozenTaggedFamilyInputBudget]; positivity
  have hfc0 : 0 ≤ fc := by dsimp only [fc]; positivity
  have hco0 : 0 ≤ co := by dsimp only [co]; positivity
  have hpr0 : 0 ≤ pr := by dsimp only [pr]; positivity
  have hmh0 : 0 ≤ mh := by dsimp only [mh, quotientInducedMarkHeightBudget]; positivity
  have hmi0 : 0 ≤ mi := by dsimp only [mi]; positivity
  have hmb0 : 0 ≤ mb := by dsimp only [mb]; positivity
  have hjgSq0 : 0 ≤ jg ^ 2 := sq_nonneg _
  have hprPow0 : 0 ≤ (pr + 2) ^ 4 := by positivity
  have hapg0 : 0 ≤ apg := by dsimp only [apg]; positivity
  have hajg0 : 0 ≤ ajg := by dsimp only [ajg]; positivity
  have haad0 : 0 ≤ aad := by dsimp only [aad]; positivity
  have habd0 : 0 ≤ abd := by dsimp only [abd]; positivity
  have halc0 : 0 ≤ alc := by
    dsimp only [alc, allocatedFrozenTaggedPairBudget, fixedAdaptedSymbolTransferInput]
    positivity
  have hajc0 : 0 ≤ ajc := by dsimp only [ajc, allocatedFrozenTaggedFamilyInputBudget]; positivity
  have hafc0 : 0 ≤ afc := by dsimp only [afc]; positivity
  have haco0 : 0 ≤ aco := by dsimp only [aco]; positivity
  have hapr0 : 0 ≤ apr := by dsimp only [apr]; positivity
  have hami0 : 0 ≤ ami := (nativeOptionFixedSourceQuotientMarkInput_bounds hgeometry).1
  have hamb0 : 0 ≤ amb := by dsimp only [amb]; positivity
  have hterminal0 : 0 ≤ terminal := by dsimp only [terminal]; positivity
  have hpg : apg ≤ pg := by dsimp only [apg, pg]; gcongr
  have hjg : ajg ≤ jg := by dsimp only [ajg, jg]; gcongr
  have had : aad ≤ ad := by dsimp only [aad, ad]; gcongr
  have hbd : abd ≤ bd := by dsimp only [abd, bd]; gcongr
  have hlc : alc ≤ lc :=
    allocatedFrozenTaggedPairBudget_mono s Cpair Cbasis hapg0 hfactor hpg hfactor_le
  have hjc : ajc ≤ jc := allocatedFrozenTaggedFamilyInputBudget_mono habd0 hbd hlc
  have hfc : afc ≤ fc := by dsimp only [afc, fc]; gcongr
  have hco : aco ≤ co := by dsimp only [aco, co]; gcongr
  have hpr : apr ≤ pr := by
    dsimp only [apr, pr]
    rw [max_eq_left haco0]
    exact add_le_add (add_le_add hco had) le_rfl
  have hmh : quotientInducedMarkHeightBudget actualGeometry ≤ mh :=
    quotientInducedMarkHeightBudget_mono hgeometry hgeometry_le
  have hmi : ami ≤ mi := by
    dsimp only [ami, nativeOptionFixedSourceQuotientMarkInput, mi]
    change ajg + quotientInducedMarkHeightBudget actualGeometry ≤ jg + mh + ad + 2
    linarith only [hjg, hmh, had0]
  have hmb : amb ≤ mb := by dsimp only [amb, mb]; gcongr
  have hpow4 : (apr + 2) ^ 4 ≤ (pr + 2) ^ 4 := by gcongr
  clear_value pg jg ad bd lc jc fc co pr mh mi mb apg ajg aad abd alc ajc afc aco apr ami amb
  have hterminal : terminal ≤ ci := by
    dsimp only [terminal, ci]
    linarith only [hpow4, hmi, hmb, hjg, hvariables, hp, hg, hpg0, hjg0, hjgSq0,
      had0, hbd0, hf, hco0, hpr0, hmh0]
  have hmi_ci : mi ≤ ci := by
    dsimp only [ci]
    linarith only [hp, hg, hpg0, hjg0, hjgSq0, had0, hbd0, hf, hco0,
      hpr0, hprPow0, hmh0, hmb0]
  have hnative : (apr + 2) ^ 3 + aco ≤ ci := by
    have hpow3base : (apr + 2) ^ 3 ≤ (pr + 2) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (add_le_add hpr (le_refl 2)) 3
    have hpow3 : (apr + 2) ^ 3 ≤ (pr + 2) ^ 4 :=
      hpow3base.trans (pow_le_pow_right₀
        (by linarith only [hpr0] : 1 ≤ pr + 2) (by decide : 3 ≤ 4))
    dsimp only [ci]
    linarith only [hpow3, hco, hp, hg, hpg0, hjg0, hjgSq0, had0, hbd0,
      hf, hpr0, hmh0, hmi0, hmb0]
  have hlong : max cost initialShort ≤ lt := by
    have hpair : (actualFactor + 2 + Cpair) ^ Cpair + 7 * actualFactor + 22 ≤
        (factor + 2 + Cpair) ^ Cpair + 7 * factor + 22 := by gcongr
    have hfull : (afc + 2) ^ T ≤ (fc + 2) ^ T := by gcongr
    have hpair0 : 0 ≤ (factor + 2 + Cpair) ^ Cpair + 7 * factor + 22 := by positivity
    have hfull0 : 0 ≤ (fc + 2) ^ T := by positivity
    dsimp only [lt, initialShort]
    apply max_le
    · linarith only [hcost, hpair0, hfull0]
    · apply max_le <;> linarith only [hpair, hfull, hpair0, hfull0, hp]
  have hp_ci : p ≤ ci := by
    dsimp only [ci]
    linarith only [hg, hpg0, hjg0, hjgSq0, had0, hbd0, hf, hco0,
      hpr0, hprPow0, hmh0, hmi0, hmb0]
  have hg_ci : geom ≤ ci := by
    dsimp only [ci]
    linarith only [hp, hpg0, hjg0, hjgSq0, had0, hbd0, hf, hco0,
      hpr0, hprPow0, hmh0, hmi0, hmb0]
  have had_ci : ad ≤ ci := by
    dsimp only [ci]
    linarith only [hp, hg, hpg0, hjg0, hjgSq0, hbd0, hf, hco0,
      hpr0, hprPow0, hmh0, hmi0, hmb0]
  have haprPow0 : 0 ≤ (apr + 2) ^ 4 := by positivity
  have hambTerminal : amb ≤ terminal := by
    dsimp only [terminal]
    linarith only [haprPow0, hami0, hajg0, hvariables0]
  have hajgTerminal : ajg ≤ terminal := by
    dsimp only [terminal]
    linarith only [haprPow0, hami0, hamb0, hvariables0]
  have haprTerminal : (apr + 2) ^ 4 ≤ terminal := by
    dsimp only [terminal]
    linarith only [hami0, hamb0, hajg0, hvariables0]
  exact ⟨⟨hterminal0, hterminal⟩,
    allocatedCandidateCommonFastBudget_mono s hterminal0 hterminal, hlong, hnative,
    ⟨hami0, hmi.trans hmi_ci⟩, ⟨haco0, hco⟩, hp_ci, hgeometry_le.trans hg_ci,
    had.trans had_ci, hambTerminal.trans hterminal, hajgTerminal.trans hterminal,
    haprTerminal.trans hterminal, hcost.trans hp_ci⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open RationalFilteredNilmanifold

theorem exists_candidateFrontActual_power_budget
    (s Cdesc Cgeometry Cpair Cbasis K T Cmark : ℕ) :
    ∃ Ctotal : ℕ, 2 ≤ Ctotal ∧ ∀ m : ℕ, ∀ p : ℝ, 0 ≤ p → (m : ℝ) ≤ p →
    ∀ cost nVariables nPivot mass0 : ℝ,
    cost ≤ p → nVariables ∈ Set.Icc 0 p → nPivot ∈ Set.Icc 0 p → mass0 ≤ p →
    let vertical := verticalDecompositionBudget (3 * p + 1)
    let factor := 2 * p + vertical + 2
    let geometry := p + (p + 2) ^ Cdesc + 2
    let pairGeo := (geometry + 2) ^ 2
    let jointGeo := (geometry + 3) ^ 2
    let adapted := (jointGeo + 2) ^ Cgeometry
    let bnd := adapted + (pairGeo + 3) ^ 5 + pairGeo + jointGeo + geometry + factor + 2
    let localCost := allocatedFrozenTaggedPairBudget s Cpair Cbasis pairGeo factor
    let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
    let fullCost := jointCost + (jointCost + K) ^ K
    let common := (fullCost + 2) ^ T + (((fullCost + 2) ^ 2 + 2) ^ 63 + 1) + fullCost + 1
    let projected := max common 0 + adapted + 1
    let markInput := nativeOptionFixedSourceQuotientMarkInput geometry
    let markBudget := (markInput + 2) ^ Cmark
    let terminal := (projected + 2) ^ 4 + markInput + markBudget + jointGeo + nVariables + 2
    let initialShort := max ((factor + 2 + Cpair) ^ Cpair + 7 * factor + 22)
      ((fullCost + 2) ^ T)
    let nativeInput := (projected + 2) ^ 3 + common
    let B := (p + 2) ^ Ctotal
    terminal ∈ Set.Icc 0 B ∧
      allocatedCandidateCommonFastBudget s terminal ≤ B ∧
      max cost initialShort ≤ B ∧
      nativeInput ≤ B ∧
      markInput ∈ Set.Icc 0 B ∧
      0 ≤ common ∧
      vertical * nPivot + ((common + 2) ^ 5 + common) + mass0 ≤ B ∧
      (s : ℝ) * (markInput * m) ≤ B ∧
      p ≤ B ∧ geometry ≤ B ∧ adapted ≤ B ∧ markBudget ≤ B ∧
      jointGeo ≤ B ∧ (projected + 2) ^ 4 ≤ B ∧ cost ≤ B := by
  obtain ⟨Cbase, hCbase, hpower⟩ := exists_candidateFrontFactor_power_budget
    s Cdesc Cgeometry Cpair Cbasis K T Cmark
  refine ⟨Cbase + s + 1, hCbase.trans (by omega), ?_⟩
  intro m p hp hm cost nVariables nPivot mass0 hcost hvariables hpivot hmass
    vertical factor geometry pairGeo jointGeo adapted bnd localCost jointCost
    fullCost common projected markInput markBudget terminal initialShort nativeInput B
  let envelopeProjected := common + adapted + 1
  let envelopeMarkHeight := quotientInducedMarkHeightBudget geometry
  let envelopeMarkInput := jointGeo + envelopeMarkHeight + adapted + 2
  let envelopeMarkBudget := (envelopeMarkInput + 2) ^ Cmark
  let commonInput := p + geometry + pairGeo + jointGeo + jointGeo ^ 2 + adapted + bnd + factor +
    common + envelopeProjected + (envelopeProjected + 2) ^ 4 + envelopeMarkHeight +
    envelopeMarkInput + envelopeMarkBudget + 2
  let fast := allocatedCandidateCommonFastBudget s commonInput
  let longThreshold := (factor + 2 + Cpair) ^ Cpair + 7 * factor + 22 +
    (fullCost + 2) ^ T + p + 1
  let massLog := p + vertical * p + ((common + 2) ^ 5 + common)
  have hpoly := hpower p hp
  change commonInput ∈ Set.Icc 0 ((p + 2) ^ Cbase) ∧
    fast ∈ Set.Icc 0 ((p + 2) ^ Cbase) ∧
    longThreshold ∈ Set.Icc 0 ((p + 2) ^ Cbase) ∧
    massLog ∈ Set.Icc 0 ((p + 2) ^ Cbase) at hpoly
  obtain ⟨hci, hfast, hlong, hmassLog⟩ := hpoly
  have hvertical : 0 ≤ vertical :=
    verticalDecompositionBudget_nonneg (by linarith only [hp])
  have hfactor : 0 ≤ factor := by dsimp only [factor]; positivity
  have hgeometry : 0 ≤ geometry := by dsimp only [geometry]; positivity
  have hactual := candidateFrontFactor_actual_bounds s Cgeometry Cpair Cbasis K T Cmark
    (factor := factor) (geom := geometry) hp hfactor hgeometry le_rfl le_rfl
    hcost hvariables.1 hvariables.2
  change terminal ∈ Set.Icc 0 commonInput ∧
    allocatedCandidateCommonFastBudget s terminal ≤ fast ∧
    max cost initialShort ≤ longThreshold ∧
    nativeInput ≤ commonInput ∧
    markInput ∈ Set.Icc 0 commonInput ∧
    common ∈ Set.Icc 0 common ∧
    p ≤ commonInput ∧ geometry ≤ commonInput ∧ adapted ≤ commonInput ∧
    markBudget ≤ commonInput ∧ jointGeo ≤ commonInput ∧
    (projected + 2) ^ 4 ≤ commonInput ∧ cost ≤ commonInput at hactual
  obtain ⟨hterminal, hfastActual, hshort, hnative, hmark, hcommon,
    hpci, hgeoci, hadapted, hmarkBudget, hjoint, hprojected, hcostci⟩ := hactual
  have hB : (p + 2) ^ Cbase ≤ B :=
    pow_le_pow_right₀ (by linarith only [hp]) (by omega)
  have hciB : commonInput ≤ B := hci.2.trans hB
  have hmassActual : vertical * nPivot + ((common + 2) ^ 5 + common) + mass0 ≤ massLog :=
    candidateFrontFactor_massLog_le hvertical le_rfl hpivot.1 hpivot.2
      hcommon.1 le_rfl hmass
  have hblock : (s : ℝ) * (markInput * m) ≤ B :=
    candidateFrontFactor_uniform_block_le_power s Cbase hp hm hmark.2 hci.2
  exact ⟨⟨hterminal.1, hterminal.2.trans hciB⟩,
    hfastActual.trans (hfast.2.trans hB), hshort.trans (hlong.2.trans hB),
    hnative.trans hciB, ⟨hmark.1, hmark.2.trans hciB⟩, hcommon.1,
    hmassActual.trans (hmassLog.2.trans hB), hblock,
    hpci.trans hciB, hgeoci.trans hciB, hadapted.trans hciB, hmarkBudget.trans hciB,
    hjoint.trans hciB, hprojected.trans hciB, hcostci.trans hciB⟩

end Erdos3.VectorPolynomial

end

end OAI

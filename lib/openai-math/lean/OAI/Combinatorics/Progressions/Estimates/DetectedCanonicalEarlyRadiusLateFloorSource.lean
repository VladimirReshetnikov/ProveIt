import OAI.Combinatorics.Progressions.Estimates.PreparedModularGeneralProductivityEarlyGain

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ uG uI uB
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

private theorem exists_preparedCanonicalGeometry_extra_budget (A C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {P Eextra : ℝ}, 0 ≤ P → 0 ≤ Eextra →
      let Q := P + (2 * P + A) ^ A + 2
      0 ≤ Q ∧ P ≤ Q ∧ (P + P + A) ^ A ≤ Q ∧
        (Q + Eextra + C) ^ C ≤ (P + Eextra + D) ^ D := by
  obtain ⟨D, hD, hbound⟩ := exists_preparedCanonicalGeometry_budget A C
  refine ⟨D, hD, ?_⟩
  intro P Eextra hP hE Q
  obtain ⟨hQ, hPQ, hAQ, _⟩ := hbound hP
  refine ⟨hQ, hPQ, hAQ, ?_⟩
  have hpow : (2 * P + A) ^ A ≤ (2 * (P + Eextra) + A) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) A
  have hbase : Q + Eextra + C ≤
      (P + Eextra) + (2 * (P + Eextra) + A) ^ A + 2 + C := by
    dsimp only [Q]
    linarith only [hpow]
  exact (pow_le_pow_left₀
    (add_nonneg (add_nonneg hQ hE) (Nat.cast_nonneg C)) hbase C).trans
      (hbound (add_nonneg hP hE)).2.2.2

private theorem chart_budget_le_exp {a v r p : ℝ}
    (ha : 1 ≤ a) (hv : 0 ≤ v) (hr : 0 < r) (hinv : r⁻¹ ≤ Real.exp p)
    (hbudget : a * (v * r) ≤ 1 / 4) : v ≤ Real.exp p := by
  have hmul : v * r ≤ a * (v * r) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (mul_nonneg hv hr.le)
  have hunit : v * r ≤ 1 := hmul.trans (hbudget.trans (by norm_num))
  exact ((le_div_iff₀ hr).mpr hunit).trans (by simpa only [one_div] using hinv)

private theorem coefficient_count_add_one_le_support {K : Type*} [Fintype K]
    (s h : ℕ) {T : ℝ}
    (hsource : (Fintype.card (BoundedCoefficientExponent K h) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
        ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ h) ≤ T) :
    (Fintype.card (BoundedCoefficientExponent K h) : ℝ) + 1 ≤ T := by
  have hc : (1 : ℝ) ≤ Fintype.card (BoundedCoefficientExponent K h) := by
    have hpos : 0 < Fintype.card (BoundedCoefficientExponent K h) :=
      Fintype.card_pos_iff.mpr ⟨⟨0, by simp⟩⟩
    exact_mod_cast hpos
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ Fintype.card (Fin (s + 1)) := by
    rw [Fintype.card_fin, pow_succ]
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
    linarith
  have hone : (1 : ℝ) ≤ (((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ h) :=
    one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hfactor : (2 : ℝ) ≤ (2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
      (((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ h) := by
    simpa only [mul_one] using mul_le_mul htwo hone (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ Fintype.card (Fin (s + 1)))
  have hmult := mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg
    (Fintype.card (BoundedCoefficientExponent K h)))
  linarith

theorem exists_detected_canonical_native_source_early_radius (m s Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type uG} [Fintype G] [DecidableEq G]
      {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type uB) [∀ b, Fintype (B b)] [∀ b, DecidableEq (B b)]
      {Bstruct pnum pSlice Qstride : ℝ} {nX : ℕ},
      0 < m → s ≤ m → 0 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum →
      (∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) → (∀ j, (n j : ℝ) ≤ pnum) →
      (∀ b : LayerSamplerAxis I n,
        (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b)) →
      pSlice ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct → (nX : ℝ) ≤ Bstruct →
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{uG,uI,uB,0} m)
      let radiusBudget := Bstruct + (2 * Bstruct + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let D := allocatedComparisonDimension m pnum
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 radiusBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
            ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Bstruct) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) (fun j => (rowSets j : Type)) D ∧
      ∀ {u P Eextra : ℝ}, 0 ≤ u → Bstruct + u ≤ P → 0 ≤ Eextra →
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let target := gainLog + 32 + Eextra
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
      let F := pDetect + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let budget := (P + Eextra + C) ^ C
      pRadius ≤ budget ∧ (∀ j, T j ≤ Real.exp budget) ∧
      2 * (siteRadius : ℝ) ≤ Real.exp budget ∧ radiusBudget ≤ Pearly ∧
      P ≤ Pearly ∧ Pearly ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
      aDetect ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧ Tmod ∈ Set.Icc 0 budget ∧
      ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
        (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧
          (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp budget) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
        t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp budget ∧
        AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B
          (fun j : Fin m => (Subtype.val :
            boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) → Finset (Fin (s + 1))))
          δ η ρ t htone ∧
        ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
          (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
          let Pscale := pRadius + Ptail
          let scaleLog := (D + Pscale + Prho + Pk + target + F + Tmod + K) ^ K
          Pscale ∈ Set.Icc 0 budget ∧ scaleLog ∈ Set.Icc 0 budget ∧
          ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
            (∀ j, (R j)⁻¹ ≤ Real.exp Pscale) ∧
            (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp Pscale) ∧
            (∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
              (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp Pscale) ∧
            Real.exp (allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod) ≤ S.value ∧
            (S.value : ℝ) ≤ Real.exp budget ∧
            ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
              scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{uG,uI,uB,0} m)
  obtain ⟨Cscale, hCscale, hscales⟩ :=
    exists_detected_uniform_early_canonical_native_source_scales.{uJ,uQ,uG,uI,uB} m s Cdetect
  obtain ⟨C, hC, hcompose⟩ := exists_preparedCanonicalGeometry_extra_budget A Cscale
  refine ⟨C, hC, ?_⟩
  intro G _ _ I _ n B _ _ Bstruct pnum pSlice Qstride nX hm hs hB hnum
    hvars hI hn hblocks hpSlice hQstride hnX A' radiusBudget rowSets T siteRadius D
  have hdim : Fintype.card (Fin (s + 1)) ≤ m + 1 := by simpa using Nat.succ_le_succ hs
  have hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j => (rowSets j : Type)) D :=
    allocatedComparisonDimensions_of_primitive (G := G) B
      (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1)))) hdim
      (fun _ => Subtype.val_injective) hnum.1 hvars hI hn
  let : ∀ j : Fin m, Nonempty (rowSets j) := fun j =>
    ⟨⟨∅, (mem_boundedBooleanJetRows (j.val + 1) ∅).mpr (by simp)⟩⟩
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource, hTradius, hsmall⟩ :=
    (Classical.choose_spec (exists_allocatedCanonicalSlice_early_radius.{uG,uI,uB,0} m)).2
      (G := G) B rowSets hB hB hdim (hvars.trans hnum.2)
      (fun j => (hI j).trans hnum.2) (fun j => (hn j).trans hnum.2)
  have hRadBase : (Bstruct + Bstruct + A') ^ A' ≤ radiusBudget := by
    change (Bstruct + Bstruct + A') ^ A' ≤ Bstruct + (2 * Bstruct + A') ^ A' + 2
    rw [show Bstruct + Bstruct = 2 * Bstruct by ring]
    linarith only [hB]
  have hpRadiusEarly : pRadius ∈ Set.Icc 0 radiusBudget :=
    ⟨hpRadius.1, hpRadius.2.trans hRadBase⟩
  have hOne := hsmall (fun _ => 1) (fun _ => by norm_num) (fun _ => Real.one_le_exp hB)
  have hTbound (j) : T j ≤ Real.exp pRadius := by
    have ha : 1 ≤ (Fintype.card (I j) : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    apply chart_budget_le_exp ha (hT0 j) (hR j).1 (hR j).2.2
    simpa only [one_mul] using hOne.2.1 j
  have hrbound : 2 * (siteRadius : ℝ) ≤ Real.exp pRadius := by
    let j : Fin m := ⟨0, hm⟩
    have ha : 1 ≤ (Fintype.card (I j) : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hb : 1 ≤ ((rowSets j).card : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hc : (1 : ℝ) ≤ Fintype.card (Finset (Fin (s + 1))) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Finset (Fin (s + 1)))))
    have hfactor : 1 ≤ (((rowSets j).card : ℝ) + 1) *
        ((Fintype.card (Finset (Fin (s + 1))) : ℝ) * ((Fintype.card (I j) : ℝ) + 1)) :=
      one_le_mul_of_one_le_of_one_le hb (one_le_mul_of_one_le_of_one_le hc ha)
    apply chart_budget_le_exp hfactor (mul_nonneg (by norm_num) siteRadius.coe_nonneg) (hR j).1
      (hR j).2.2
    simpa only [mul_assoc, one_mul] using hOne.2.2 j
  refine ⟨pRadius, R, hpRadiusEarly, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro u P Eextra hu hmaster hExtra Pearly pModel pDetect aDetect gainLog target Pk F Tmod
    δ E η Prho Ptail K budget
  have hBP : Bstruct ≤ P := (le_add_of_nonneg_right hu).trans hmaster
  have hP : 0 ≤ P := hB.trans hBP
  have huP : u ≤ P := (le_add_of_nonneg_left hB).trans hmaster
  have hRadiusEarly : radiusBudget ≤ Pearly := by
    have hpow : (2 * Bstruct + A') ^ A' ≤ (2 * P + A') ^ A' :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hBP]) _
    exact add_le_add (add_le_add hBP hpow) (le_refl 2)
  have hcompose' := hcompose hP hExtra
  change 0 ≤ Pearly ∧ P ≤ Pearly ∧ (P + P + A') ^ A' ≤ Pearly ∧
    (Pearly + Eextra + Cscale) ^ Cscale ≤ budget at hcompose'
  obtain ⟨hPearly, hPEarly, _, hScaleBudget⟩ := hcompose'
  have hpRadiusPearly : pRadius ∈ Set.Icc 0 Pearly :=
    ⟨hpRadiusEarly.1, hpRadiusEarly.2.trans hRadiusEarly⟩
  have hactual := hscales (G := G) B (P := Pearly) hm hs hPearly hExtra
    ⟨hnum.1, hnum.2.trans (hBP.trans hPEarly)⟩ hvars hI hn hblocks
    ⟨hpSlice.1, hpSlice.2.trans (hBP.trans hPEarly)⟩ ⟨hu, huP.trans hPEarly⟩
    ⟨hQstride.1, hQstride.2.trans (hBP.trans hPEarly)⟩ (hnX.trans (hBP.trans hPEarly))
  obtain ⟨hPbudget, hpModel, hpDetect, haDetect, htarget, hD,
    hgain, hPk, hPrho, hPtail, hTmod, ρ, hρ, t, ht, htone, htinv, htbudget, hcomparison, hsampler⟩ := hactual
  have hPearlyBudget : Pearly ≤ budget := hPbudget.trans hScaleBudget
  have hRadBudget : pRadius ≤ budget := hpRadiusPearly.2.trans hPearlyBudget
  have hexp : Real.exp ((Pearly + Eextra + Cscale) ^ Cscale) ≤ Real.exp budget :=
    Real.exp_le_exp.mpr hScaleBudget
  refine ⟨hRadBudget,
    fun j => (hTbound j).trans (Real.exp_le_exp.mpr hRadBudget),
    hrbound.trans (Real.exp_le_exp.mpr hRadBudget), hRadiusEarly, hPEarly, hPearlyBudget,
    ⟨hpModel.1, hpModel.2.trans hScaleBudget⟩,
    ⟨hpDetect.1, hpDetect.2.trans hScaleBudget⟩,
    ⟨haDetect.1, haDetect.2.trans hScaleBudget⟩,
    ⟨htarget.1, htarget.2.trans hScaleBudget⟩,
    ⟨hD.1, hD.2.trans hScaleBudget⟩,
    ⟨hgain.1, hgain.2.trans hScaleBudget⟩,
    ⟨hPk.1, hPk.2.trans hScaleBudget⟩,
    ⟨hPrho.1, hPrho.2.trans hScaleBudget⟩,
    ⟨hPtail.1, hPtail.2.trans hScaleBudget⟩,
    ⟨hTmod.1, hTmod.2.trans hScaleBudget⟩, ρ,
    fun partition => ⟨(hρ partition).1, (hρ partition).2.1, (hρ partition).2.2.1,
      (hρ partition).2.2.2.trans hexp⟩,
    t, ht, htone, htinv, htbudget.trans hexp, hcomparison, ?_⟩
  intro J _ U basis Pscale scaleLog
  obtain ⟨hPscale, hScaleLog, S, hRinv, htinv', hlength, hS, hcutoff⟩ :=
    hsampler U basis R (fun j => (hR j).1) hpRadiusPearly (fun j => (hR j).2.2)
  exact ⟨⟨hPscale.1, hPscale.2.trans hScaleBudget⟩,
    ⟨hScaleLog.1, hScaleLog.2.trans hScaleBudget⟩, S, hRinv, htinv',
    fun j => ((coefficient_count_add_one_le_support s (j.val + 1) (hTsource j)).trans
      (hTbound j)).trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right hPtail.1)),
    hlength, hS.trans hexp, hcutoff⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

private theorem allocatedAffineLengthLog_prepared_density_fin
    (m nX : ℕ) (D P Prho Pk target p Qstride : ℝ) :
    Real.exp (allocatedAffineLengthLog m D P Prho Pk target (p + 1)
      (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤
    Real.exp (allocatedAffineLengthLog m D P Prho Pk target (p + 2)
      (((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride)) := by
  simp only [Fintype.card_fin]
  exact Real.exp_le_exp.mpr (allocatedAffineLengthLog_prepared_density m D P Prho Pk target p _)

private theorem preparedComparison_eta_bound (target cost : ℝ) :
    Real.exp (-(target + cost + 5)) ≤ Real.exp (-(target + 1 + cost + 4)) := by
  apply Real.exp_le_exp.mpr
  linarith only

theorem exists_detected_canonical_early_radius_late_floor_source (m s Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type) [∀ b, Fintype (B b)] [∀ b, DecidableEq (B b)]
      {Bstruct pnum pSlice Qstride : ℝ} {nX : ℕ},
      0 < m → s ≤ m → 0 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum →
      (∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) → (∀ j, (n j : ℝ) ≤ pnum) →
      (∀ b : LayerSamplerAxis I n,
        (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b)) →
      pSlice ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct → (nX : ℝ) ≤ Bstruct →
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let radiusBudget := Bstruct + (2 * Bstruct + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let D := allocatedComparisonDimension m pnum
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 radiusBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
            ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Bstruct) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) (fun j => (rowSets j : Type)) D ∧
      ∀ {u P Eextra : ℝ}, 0 ≤ u → Bstruct + u ≤ P → 0 ≤ Eextra →
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let target := gainLog + 32 + Eextra
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
      let F := pDetect + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let budget := (P + Eextra + C) ^ C
      pRadius ≤ budget ∧ (∀ j, T j ≤ Real.exp budget) ∧
      2 * (siteRadius : ℝ) ≤ Real.exp budget ∧ radiusBudget ≤ Pearly ∧
      P ≤ Pearly ∧ Pearly ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
      aDetect ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧ Tmod ∈ Set.Icc 0 budget ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp budget ∧
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ},
        1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        let Pscale := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          Pscale ∈ Set.Icc 0 budget ∧ Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp
            (allocatedWitnessScaleLog budget Qw + (1 + budget ^ 2) * Pmin) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          Nonempty (AllocatedEarlyNativeSourceGeometryGeneral (B := B) (U := U)
            (basis := basis) (S := S) (s := s) (nX := nX)
            Bstruct Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1)) ∧
            (scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  obtain ⟨C, hC, hearly⟩ :=
    exists_detected_canonical_native_source_early_radius.{0,0,0,0,0} m s Cdetect
  refine ⟨C, hC, ?_⟩
  intro G _ _ I _ n B _ _ Bstruct pnum pSlice Qstride nX hm hs hB hnum
    hvars hI hn hblocks hpSlice hQstride hnX A radiusBudget rowSets T siteRadius D
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hsource⟩ :=
    hearly (G := G) B hm hs hB hnum hvars hI hn hblocks hpSlice hQstride hnX
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro u P Eextra hu hmaster hExtra Pearly pModel pDetect aDetect gainLog target Pk F Tmod
    δ E η Prho Ptail K budget
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      ρ, hρ, t, ht, htone, htPtail, htbudget, hcomparison, hsamplers⟩ :=
    hsource hu hmaster hExtra
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    t, ht, htone, htPtail, htbudget, ?_⟩
  intro Lmin W Qw Pmin hW hQw hWexp hPmin hLmin J _ U basis Pscale
  obtain ⟨hPscale, hScaleLog, S₀, hRinv, htinv', hcount, hlength, hS₀, hcutoff⟩ :=
    hsamplers U basis
  have hexp := Real.exp_le_exp.mpr hPscale.2
  obtain ⟨S, hS₀S, hfloor, hS, hwidth⟩ :=
    exists_allocatedWitnessScale_with_late_floor B U basis R (fun _ => t) S₀ Lmin
      hdimensions hD.2 (fun j => (hR j).1) (fun _ => ht)
      (fun j => (hRinv j).trans hexp) (fun j => (htinv' j).trans hexp)
      hS₀ hW hQw hWexp hPmin hLmin
  have hD1 : 1 ≤ D := by
    have hdim := (allocatedComparisonDimension_bounds m hnum.1).2.1
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
    exact hm1.trans hdim
  have hkTail : Pk ≤ Ptail :=
    prepared_affineProfileToleranceEnvelope_kernel_bound hm
      canonicalSublevelCutoffLip canonicalTransitionLip hD1 hPk.1 htarget.1 hDetect.1
  have hkScale : Pk ≤ Pscale := hkTail.trans (le_add_of_nonneg_left hpRadius.1)
  refine ⟨S, hPscale, hkScale, hfloor, hS, hwidth, ?_, ?_⟩
  · refine allocatedEarlyNativeSourceGeometryGeneral_of_fields B U basis S
      Bstruct Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))
      hPscale.1 (fun j => (hR j).2.1.trans (Real.one_le_exp hPscale.1))
      hRinv htinv' hcount hdimensions hPk.1 hPrho.1 htarget.1 ?_
      η (Real.exp_pos _).le ?_ ρ t htone (@hcomparison)
      (fun partition => (hρ partition).1) (fun partition => (hρ partition).2.1)
      (fun partition => (hρ partition).2.2.1) (fun _ => le_rfl)
      T hTideal hTsource siteRadius hrone hTradius hsmall
      (fun j => (hR j).2.2.trans (Real.le_coe_toNNReal _))
    · exact (allocatedAffineLengthLog_prepared_density_fin
        m nX D Pscale Prho Pk target pDetect Qstride).trans
          (hlength.trans (Nat.cast_le.mpr hS₀S))
    · exact preparedComparison_eta_bound target (D * ((m * 2 ^ (m + 1) : ℕ) * Pk))
  · intro α hα
    exact ⟨slicedDetectionGain_lower s Cdetect _ hα,
      slicedDetection_kernel_cutoff_bound s Cdetect _ G hDetect.1 hDetect.1 hAlog.1 hα,
      (hcutoff α hα).trans hS₀S⟩

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Dynamics.PreparedDetectedCanonicalNativeSourceScaleBudget
import OAI.Combinatorics.Progressions.Dynamics.PreparedSameScaleBadProductBudget

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

theorem exists_detected_canonical_native_source_geometry (m s Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type uG} [Fintype G] [DecidableEq G]
      {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type uB) [∀ b, Fintype (B b)] [∀ b, DecidableEq (B b)]
      {P pnum pSlice u Qstride Eextra : ℝ} {nX : ℕ},
      0 < m → s ≤ m → 0 ≤ P → 0 ≤ Eextra → pnum ∈ Set.Icc 0 P →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum →
      (∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) → (∀ j, (n j : ℝ) ≤ pnum) →
      (∀ b : LayerSamplerAxis I n,
        (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b)) →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{uG,uI,uB,0} m)
      let Pearly := P + (2 * P + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
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
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ budget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
            ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ j, T j ≤ Real.exp budget) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp budget ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp P) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) (fun j => (rowSets j : Type)) D ∧
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
  obtain ⟨Cscale, hCscale, hscales⟩ := exists_detected_uniform_early_canonical_native_source_scales.{uJ,uQ,uG,uI,uB} m s Cdetect
  obtain ⟨C, hC, hcompose⟩ := exists_preparedCanonicalGeometry_extra_budget A Cscale
  refine ⟨C, hC, ?_⟩
  intro G _ _ I _ n B _ _ P pnum pSlice u Qstride Eextra nX hm hs hP hExtra hnum
    hvars hI hn hblocks hpSlice hu hQstride hnX A' Pearly rowSets T siteRadius pModel pDetect aDetect D gainLog target Pk F Tmod
    δ E η Prho Ptail K budget
  have hcompose' := hcompose hP hExtra
  change 0 ≤ Pearly ∧ P ≤ Pearly ∧ (P + P + A') ^ A' ≤ Pearly ∧
    (Pearly + Eextra + Cscale) ^ Cscale ≤ budget at hcompose'
  obtain ⟨hPearly, hPEarly, hRadiusEarly, hScaleBudget⟩ := hcompose'
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
      (G := G) B rowSets hP hP hdim
      (hvars.trans hnum.2)
      (fun j => (hI j).trans hnum.2)
      (fun j => (hn j).trans hnum.2)
  have hpRadiusEarly : pRadius ∈ Set.Icc 0 Pearly := ⟨hpRadius.1, hpRadius.2.trans hRadiusEarly⟩
  have hactual := hscales (G := G) B (P := Pearly) hm hs hPearly hExtra
    ⟨hnum.1, hnum.2.trans hPEarly⟩ hvars hI hn hblocks
    ⟨hpSlice.1, hpSlice.2.trans hPEarly⟩ ⟨hu.1, hu.2.trans hPEarly⟩
    ⟨hQstride.1, hQstride.2.trans hPEarly⟩ (hnX.trans hPEarly)
  obtain ⟨hPbudget, hpModel, hpDetect, haDetect, htarget, hD,
    hgain, hPk, hPrho, hPtail, hTmod, ρ, hρ, t, ht, htone, htinv, htbudget, hcomparison, hsampler⟩ := hactual
  have hPearlyBudget : Pearly ≤ budget := hPbudget.trans hScaleBudget
  have hRadBudget : pRadius ≤ budget := hpRadiusEarly.2.trans hPearlyBudget
  have hexp : Real.exp ((Pearly + Eextra + Cscale) ^ Cscale) ≤ Real.exp budget :=
    Real.exp_le_exp.mpr hScaleBudget
  have hOne := hsmall (fun _ => 1) (fun _ => by norm_num) (fun _ => Real.one_le_exp hP)
  have hTbound (j) : T j ≤ Real.exp pRadius := by
    have ha : 1 ≤ (Fintype.card (I j) : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    apply chart_budget_le_exp ha (hT0 j) (hR j).1
      (hR j).2.2
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
  refine ⟨pRadius, R, hpRadiusEarly, hRadBudget, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound,
    fun j => (hTbound j).trans (Real.exp_le_exp.mpr hRadBudget),
    hrbound.trans (Real.exp_le_exp.mpr hRadBudget), hsmall, hdimensions, hPEarly, hPearlyBudget,
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
    hsampler U basis R (fun j => (hR j).1) hpRadiusEarly (fun j => (hR j).2.2)
  exact ⟨⟨hPscale.1, hPscale.2.trans hScaleBudget⟩,
    ⟨hScaleLog.1, hScaleLog.2.trans hScaleBudget⟩, S, hRinv, htinv',
    fun j => ((coefficient_count_add_one_le_support s (j.val + 1) (hTsource j)).trans
      (hTbound j)).trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right hPtail.1)),
    hlength, hS.trans hexp, hcutoff⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

theorem exists_preparedModularCanonicalDetectorEarlyParameters (m Cdetect : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type) [∀ b, Fintype (B b)] [∀ b, DecidableEq (B b)]
      {P pnum pSlice u Qstride : ℝ} {nX : ℕ},
      0 < m → 0 ≤ P → pnum ∈ Set.Icc 0 P →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum →
      (∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) → (∀ j, (n j : ℝ) ≤ pnum) →
      (∀ b : LayerSamplerAxis I n,
        (boundedBooleanJetRows (Fin 1) (b.1.val + 1)).card ≤ Fintype.card (B b)) →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Aradius := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := P + (2 * P + Aradius) ^ Aradius + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog 0 Cdetect
        (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin 1) G (gainLog + pDetect + 4)
      let budget := (P + A) ^ A
      P ≤ budget ∧ Pearly ∈ Set.Icc 0 budget ∧ pModel ∈ Set.Icc 0 budget ∧
        pDetect ∈ Set.Icc 0 budget ∧ aDetect ∈ Set.Icc 0 budget ∧
        D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget := by
  obtain ⟨A, hA, hgeometry⟩ := exists_detected_canonical_native_source_geometry.{0,0,0,0,0} m 0 Cdetect
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ n B _ _ P pnum pSlice u Qstride nX hm hP hnum hvars hI hn hblocks
    hpSlice hu hQstride hnX Aradius Pearly pModel pDetect aDetect D gainLog Pk budget
  have hactual := hgeometry (G := G) B (Eextra := 0) hm (Nat.zero_le m) hP
    (le_refl 0) hnum hvars hI hn hblocks hpSlice hu hQstride hnX
  obtain ⟨pRadius, R, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hPEarly,
    hEarlyBudget, hModel, hDetect, hAlog, _, hD, hGain, hPk, _⟩ := hactual
  have hEarly : Pearly ∈ Set.Icc 0 budget := by
    exact ⟨hP.trans hPEarly, by simpa only [add_zero] using hEarlyBudget⟩
  refine ⟨hPEarly.trans hEarly.2, hEarly, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [add_zero] using hModel
  · simpa only [add_zero] using hDetect
  · simpa only [add_zero] using hAlog
  · simpa only [add_zero] using hD
  · simpa only [add_zero] using hGain
  · simpa only [add_zero] using hPk

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_preparedModularGeneralCanonicalGeometry (m s Cdetect : ℕ) :
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    let Cgeom := Classical.choose (exists_detected_canonical_native_source_geometry.{uJ,uQ,0,0,0} m s Cdetect)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {P pSlice u Qstride Eextra : ℝ},
      0 < m → ∀ hs : s ≤ m, 0 ≤ P → 0 ≤ Eextra → (M : ℝ) ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Palloc := (P + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc s hs
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := Palloc + (2 * Palloc + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
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
      let geometryBudget := (Palloc + Eextra + Cgeom) ^ Cgeom
      let totalBudget := (P + Eextra + C) ^ C
      P ≤ Palloc ∧ pnum ≤ Palloc ∧ geometryBudget ≤ totalBudget ∧
      (s + 1) * (s + 3) ≤ Fintype.card G ∧
      (∀ h : ℕ, h ≤ m → h * Jalloc ≤ Fintype.card G) ∧
      (∀ a : LayerSamplerAxis I n, Jalloc ≤ Fintype.card (B a)) ∧
      (∀ a : LayerSamplerAxis I n, (rowSets a.1).card ≤ Fintype.card (B a)) ∧
      (∀ i, (selection i).val = i.val) ∧
      (∀ inactive : LayerSamplerAxis I n → Prop,
        (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput (Fin nX) I inactive j)) ≤
          nX + m * M) ∧
      ⌈2 * ((modularInitialRankStrength m (nX + m * M) : ℝ) + (nX + m * M : ℕ) + 10) /
        modularRankSmallBallExponent m⌉₊ ≤ Jalloc ∧
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ geometryBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
            ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ j, T j ≤ Real.exp geometryBudget) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp geometryBudget ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Palloc) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) (fun j => (rowSets j : Type)) D ∧
      Palloc ≤ Pearly ∧ Pearly ≤ geometryBudget ∧ pModel ∈ Set.Icc 0 geometryBudget ∧ pDetect ∈ Set.Icc 0 geometryBudget ∧
      aDetect ∈ Set.Icc 0 geometryBudget ∧ target ∈ Set.Icc 0 geometryBudget ∧ D ∈ Set.Icc 0 geometryBudget ∧ gainLog ∈ Set.Icc 0 geometryBudget ∧ Pk ∈ Set.Icc 0 geometryBudget ∧
      Prho ∈ Set.Icc 0 geometryBudget ∧ Ptail ∈ Set.Icc 0 geometryBudget ∧ Tmod ∈ Set.Icc 0 geometryBudget ∧
      ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
        (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧
          (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp geometryBudget) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
        t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp geometryBudget ∧
        AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B
          (fun j : Fin m => (Subtype.val :
            boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) → Finset (Fin (s + 1))))
          δ η ρ t htone ∧
        ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
          (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
          let Pscale := pRadius + Ptail
          let scaleLog := (D + Pscale + Prho + Pk + target + F + Tmod + K) ^ K
          Pscale ∈ Set.Icc 0 geometryBudget ∧ scaleLog ∈ Set.Icc 0 geometryBudget ∧
          ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
            (∀ j, (R j)⁻¹ ≤ Real.exp Pscale) ∧
            (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp Pscale) ∧
            (∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
              (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp Pscale) ∧
            Real.exp (allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod) ≤ S.value ∧
            (S.value : ℝ) ≤ Real.exp geometryBudget ∧
            ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
              scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  intro Aalloc Cgeom
  let Xpoly : Polynomial ℕ := Polynomial.X
  let poly : Polynomial ℕ := ((Xpoly + Polynomial.C Aalloc) ^ Aalloc + Xpoly +
    Polynomial.C Cgeom) ^ Cgeom
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord P pSlice u Qstride Eextra hm hs hP hExtra hM hpSlice hu hQstride hnX
    Jalloc pnum Palloc G I n B selection A Pearly rowSets T siteRadius pModel pDetect aDetect D
    gainLog target Pk F Tmod δ E η Prho Ptail K geometryBudget totalBudget
  obtain ⟨hPalloc, _, hnum, _⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetectorAllocationBudget m)).2 hP hM hnX
  have hPalloc0 : 0 ≤ Palloc := hP.trans hPalloc
  have hgeometryBudget : geometryBudget ≤ totalBudget := by
    have hmono : Palloc + Eextra + Cgeom ≤
        (P + Eextra + Aalloc) ^ Aalloc + (P + Eextra) + Cgeom := by
      have hpow : Palloc ≤ (P + Eextra + Aalloc) ^ Aalloc :=
        pow_le_pow_left₀ (by positivity) (by linarith) Aalloc
      linarith
    calc
      geometryBudget ≤ ((P + Eextra + Aalloc) ^ Aalloc + (P + Eextra) + Cgeom) ^ Cgeom :=
        pow_le_pow_left₀ (by positivity) hmono Cgeom
      _ ≤ totalBudget := by
        simpa [poly, Xpoly, Polynomial.eval₂_pow] using hbudget (P + Eextra) (add_nonneg hP hExtra)
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hCoord
  have hblocks (a : LayerSamplerAxis I n) :
      (rowSets a.1).card ≤ Fintype.card (B a) := by
    calc
      _ = Fintype.card (BoundedBooleanJet (Fin (s + 1)) (a.1.val + 1)) :=
        (Fintype.card_coe _).symm.trans (Fintype.card_congr (boundedBooleanJetRowsEquiv _ _))
      _ ≤ _ := enlargedPreparedCommonSamplerBlock_jets L Jalloc s hs a
  have hlift {z : ℝ} (hz : z ∈ Set.Icc 0 P) : z ∈ Set.Icc 0 Palloc :=
    ⟨hz.1, hz.2.trans hPalloc⟩
  refine ⟨hPalloc, hnum.2, hgeometryBudget,
    enlargedPreparedCommonKernel_analytic_capacity m Jalloc s hs,
    fun h hh => enlargedPreparedCommonKernel_multiple_capacity m Jalloc h hh,
    fun a => enlargedPreparedCommonSamplerBlock_allocation L Jalloc a,
    hblocks, fun _ => rfl, ?_, modularInitialBlockCount_threshold hm (nX + m * M), ?_⟩
  · intro inactive
    exact preparedCongruenceRankOutput_sum_card_fin_le L hm inactive hCoord (fun _ => le_rfl)
  · exact (Classical.choose_spec
      (exists_detected_canonical_native_source_geometry.{uJ,uQ,0,0,0} m s Cdetect)).2
      (G := G) B hm hs hPalloc0 hExtra hnum (Nat.cast_le.mpr hvars)
      (fun j => Nat.cast_le.mpr (hI j)) (fun j => Nat.cast_le.mpr (hn j))
      hblocks (hlift hpSlice) (hlift hu) (hlift hQstride) (hnX.trans hPalloc)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_preparedModularWitnessCanonicalGeometry (m s Cdetect : ℕ) :
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    let Cgeom := Classical.choose (exists_detected_canonical_native_source_geometry.{uJ,uQ,0,0,0} m s Cdetect)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {P pSlice u Qstride Eextra : ℝ},
      0 < m → ∀ hs : s ≤ m, 0 ≤ P → 0 ≤ Eextra → (M : ℝ) ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Palloc := (P + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc s hs
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := Palloc + (2 * Palloc + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
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
      let geometryBudget := (Palloc + Eextra + Cgeom) ^ Cgeom
      let totalBudget := (P + Eextra + C) ^ C
      P ≤ Palloc ∧ pnum ≤ Palloc ∧ geometryBudget ≤ totalBudget ∧
      (s + 1) * (s + 3) ≤ Fintype.card G ∧
      (∀ h : ℕ, h ≤ m → h * Jalloc ≤ Fintype.card G) ∧
      (∀ a : LayerSamplerAxis I n, Jalloc ≤ Fintype.card (B a)) ∧
      (∀ a : LayerSamplerAxis I n, (rowSets a.1).card ≤ Fintype.card (B a)) ∧
      (∀ i, (selection i).val = i.val) ∧
      (∀ inactive : LayerSamplerAxis I n → Prop,
        (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput (Fin nX) I inactive j)) ≤
          nX + m * M) ∧
      ⌈2 * ((modularInitialRankStrength m (nX + m * M) : ℝ) + (nX + m * M : ℕ) + 10) /
        modularRankSmallBallExponent m⌉₊ ≤ Jalloc ∧
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ geometryBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
            ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ j, T j ≤ Real.exp geometryBudget) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp geometryBudget ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Palloc) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) (fun j => (rowSets j : Type)) D ∧
      Palloc ≤ Pearly ∧ Pearly ≤ geometryBudget ∧ pModel ∈ Set.Icc 0 geometryBudget ∧ pDetect ∈ Set.Icc 0 geometryBudget ∧
      aDetect ∈ Set.Icc 0 geometryBudget ∧ target ∈ Set.Icc 0 geometryBudget ∧ D ∈ Set.Icc 0 geometryBudget ∧ gainLog ∈ Set.Icc 0 geometryBudget ∧ Pk ∈ Set.Icc 0 geometryBudget ∧
      Prho ∈ Set.Icc 0 geometryBudget ∧ Ptail ∈ Set.Icc 0 geometryBudget ∧ Tmod ∈ Set.Icc 0 geometryBudget ∧
      ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
        (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧
          (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp geometryBudget) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
        t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp geometryBudget ∧
        AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B
          (fun j : Fin m => (Subtype.val :
            boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) → Finset (Fin (s + 1))))
          δ η ρ t htone ∧
        ∀ {W Qw : ℝ}, 1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
          (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
          let Pscale := pRadius + Ptail
          let scaleLog := (D + Pscale + Prho + Pk + target + F + Tmod + K) ^ K
          Pscale ∈ Set.Icc 0 geometryBudget ∧ scaleLog ∈ Set.Icc 0 geometryBudget ∧
          ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
            (∀ j, (R j)⁻¹ ≤ Real.exp Pscale) ∧
            (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp Pscale) ∧
            (∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
              (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp Pscale) ∧
            Real.exp (allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod) ≤ S.value ∧
            (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog geometryBudget Qw) ∧
            (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
              8 * (probabilityProfileLipschitz : ℝ) * W ≤
                (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                  ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
            ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
              scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  intro Aalloc Cgeom
  obtain ⟨C, hC, hgeometry⟩ := exists_preparedModularGeneralCanonicalGeometry.{uJ,uQ} m s Cdetect
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord P pSlice u Qstride Eextra hm hs hP hExtra hM hpSlice hu hQstride hnX
    Jalloc pnum Palloc G I n B selection A Pearly rowSets T siteRadius pModel pDetect aDetect D
    gainLog target Pk F Tmod δ E η Prho Ptail K geometryBudget totalBudget
  obtain ⟨hPalloc, hpnum, hGeometryBudget, hcapacity, hkernelAllocation, hblockAllocation,
      hblockRows, hselection, houtputCount, hthreshold,
      pRadius, R, hpRadius, hpRadiusBudget, hR, hrone, hT0, hTideal, hTsource, hTradius,
      hTbound, hrbound, hTbudget, hrbudget, hsmall, hdimensions, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      ρ, hρ, t, ht, htone, htPtail, htbudget, hcomparison, hsamplers⟩ :=
    hgeometry L hCoord hm hs hP hExtra hM hpSlice hu hQstride hnX
  refine ⟨hPalloc, hpnum, hGeometryBudget, hcapacity, hkernelAllocation, hblockAllocation,
    hblockRows, hselection, houtputCount, hthreshold,
    pRadius, R, hpRadius, hpRadiusBudget, hR, hrone, hT0, hTideal, hTsource, hTradius,
    hTbound, hrbound, hTbudget, hrbudget, hsmall, hdimensions, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    ρ, hρ, t, ht, htone, htPtail, htbudget, hcomparison, ?_⟩
  intro W Qw hW hQw hWexp J _ U basis Pscale scaleLog
  obtain ⟨hPscale, hScaleLog, S₀, hRi, hσi, hcount, hlength, hS₀, hcutoff⟩ := hsamplers U basis
  have hexp := Real.exp_le_exp.mpr hPscale.2
  obtain ⟨S, hS₀S, hS, hwidth⟩ := exists_allocatedWitnessScale_of_bounded_source
    B U basis R (fun _ => t) S₀ hdimensions hD.2
    (fun j => (hR j).1) (fun _ => ht)
    (fun j => (hRi j).trans hexp) (fun j => (hσi j).trans hexp)
    hS₀ hW hQw hWexp
  refine ⟨hPscale, hScaleLog, S, hRi, hσi, hcount,
    hlength.trans (Nat.cast_le.mpr hS₀S), hS, hwidth, ?_⟩
  intro α hα
  exact (hcutoff α hα).trans hS₀S

end Erdos3.VectorPolynomial

end

end OAI

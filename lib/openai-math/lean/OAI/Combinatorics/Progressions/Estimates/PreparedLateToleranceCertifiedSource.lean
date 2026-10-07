import OAI.Combinatorics.Progressions.Estimates.PreparedCenteredModelMarginalData
import OAI.Combinatorics.Progressions.Estimates.PreparedShortLateFloorCertifiedBadProduct

namespace OAI

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

theorem exists_detected_canonical_early_radius_late_tolerance_source (m s Cdetect : ℕ) :
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
      ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := min t (Real.exp (-Qσ))
      let Pscale := pRadius + Ptail + Qσ
      let lengthLog := allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod
      let Pseed := allocatedScaleLog (D + Pscale + lengthLog + 1)
      0 < σ ∧ σ ≤ t ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧
      Pscale ∈ Set.Icc 0 (2 * budget + Qσ) ∧
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ},
        1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
          Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp
            (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin) ∧
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
  intro Qσ hQσ σ Pscale lengthLog Pseed
  have hσ : 0 < σ := lt_min ht (Real.exp_pos _)
  have hσt : σ ≤ t := min_le_left _ _
  have hσexp : σ ≤ Real.exp (-Qσ) := min_le_right _ _
  have hPscale0 : 0 ≤ Pscale := add_nonneg (add_nonneg hpRadius.1 hPtail.1) hQσ
  have hPold : pRadius + Ptail ≤ Pscale := le_add_of_nonneg_right hQσ
  have hσinv : σ⁻¹ ≤ Real.exp Pscale := by
    rcases le_total t (Real.exp (-Qσ)) with hle | hle
    · have heq : σ = t := min_eq_left hle
      rw [heq]
      exact htPtail.trans (Real.exp_le_exp.mpr (by
        change Ptail ≤ pRadius + Ptail + Qσ
        linarith only [hpRadius.1, hQσ]))
    · have heq : σ = Real.exp (-Qσ) := min_eq_right hle
      rw [heq, ← Real.exp_neg, neg_neg]
      exact Real.exp_le_exp.mpr (le_add_of_nonneg_left (add_nonneg hpRadius.1 hPtail.1))
  have hPscaleBudget : Pscale ≤ 2 * budget + Qσ := by
    change pRadius + Ptail + Qσ ≤ 2 * budget + Qσ
    linarith only [hpRadiusBudget, hPtail.2]
  refine ⟨hσ, hσt, hσexp, hσinv, ⟨hPscale0, hPscaleBudget⟩, ?_⟩
  intro Lmin W Qw Pmin hW hQw hWexp hPmin hLmin J _ U basis
  obtain ⟨hPoldBudget, hScaleLog, Sold, hRinvOld, htinvOld, hcountOld,
      hlengthOld, hSold, hcutoffOld⟩ := hsamplers U basis
  have hRinv (j) : (R j)⁻¹ ≤ Real.exp Pscale :=
    (hRinvOld j).trans (Real.exp_le_exp.mpr hPold)
  have hcount (j : Fin m) : (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp Pscale :=
    (hcountOld j).trans (Real.exp_le_exp.mpr hPold)
  have hF : 0 ≤ F := by change 0 ≤ pDetect + 2; linarith only [hDetect.1]
  have hL : 0 ≤ lengthLog :=
    (allocatedAffineLengthLog_bounds m hD.1 hPscale0 hPrho.1 hPk.1 htarget.1 hF hTmod.1).2.2.1
  have hQseed : 0 ≤ D + Pscale + lengthLog + 1 := by
    linarith only [hD.1, hPscale0, hL]
  have hSeedD : D ≤ Pseed :=
    (show D ≤ D + Pscale + lengthLog + 1 by linarith only [hPscale0, hL]).trans
      (le_allocatedScaleLog hQseed)
  have hSeedP : Pscale ≤ Pseed :=
    (show Pscale ≤ D + Pscale + lengthLog + 1 by linarith only [hD.1, hL]).trans
      (le_allocatedScaleLog hQseed)
  let S₀ : LayerSamplerScale (G := G) B U basis R (fun _ => σ) :=
    allocatedAffineScale B U basis (fun j => (hR j).1) (fun _ => hσ)
    D Pscale Prho Pk target F Tmod
  have hlength : Real.exp lengthLog ≤ (S₀.value : ℝ) :=
    allocatedAffineScale_lower B U basis (fun j => (hR j).1) (fun _ => hσ)
      D Pscale Prho Pk target F Tmod
  have hS₀ : (S₀.value : ℝ) ≤ Real.exp Pseed :=
    allocatedAffineScale_upper B U basis (fun j => (hR j).1) (fun _ => hσ)
      hdimensions hPscale0 hPrho.1 hPk.1 htarget.1 hF hTmod.1 hRinv (fun _ => hσinv)
  obtain ⟨S, hS₀S, hfloor, hS, hwidth⟩ :=
    exists_allocatedWitnessScale_with_late_floor B U basis R (fun _ => σ) S₀ Lmin
      hdimensions hSeedD (fun j => (hR j).1) (fun _ => hσ)
      (fun j => (hRinv j).trans (Real.exp_le_exp.mpr hSeedP))
      (fun _ => hσinv.trans (Real.exp_le_exp.mpr hSeedP))
      hS₀ hW hQw hWexp hPmin hLmin
  have hD1 : 1 ≤ D := by
    have hdim := (allocatedComparisonDimension_bounds m hnum.1).2.1
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
    exact hm1.trans hdim
  have hkTail : Pk ≤ Ptail :=
    prepared_affineProfileToleranceEnvelope_kernel_bound hm
      canonicalSublevelCutoffLip canonicalTransitionLip hD1 hPk.1 htarget.1 hDetect.1
  have hkScale : Pk ≤ Pscale :=
    (hkTail.trans (le_add_of_nonneg_left hpRadius.1)).trans hPold
  have hlengthS : Real.exp lengthLog ≤ (S.value : ℝ) :=
    hlength.trans (Nat.cast_le.mpr hS₀S)
  refine ⟨S, hkScale, hfloor, hS, hwidth, ?_, ?_⟩
  · refine allocatedEarlyNativeSourceGeometryGeneral_of_fields B U basis S
      Bstruct Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))
      hPscale0 (fun j => (hR j).2.1.trans (Real.one_le_exp hPscale0))
      hRinv (fun _ => hσinv) hcount hdimensions hPk.1 hPrho.1 htarget.1 ?_
      η (Real.exp_pos _).le ?_ ρ t htone (@hcomparison)
      (fun partition => (hρ partition).1) (fun partition => (hρ partition).2.1)
      (fun partition => (hρ partition).2.2.1) (fun _ => hσt)
      T hTideal hTsource siteRadius hrone hTradius hsmall
      (fun j => (hR j).2.2.trans (Real.le_coe_toNNReal _))
    · exact (allocatedAffineLengthLog_prepared_density_fin
        m nX D Pscale Prho Pk target pDetect Qstride).trans hlengthS
    · exact preparedComparison_eta_bound target (D * ((m * 2 ^ (m + 1) : ℕ) * Pk))
  · intro α hα
    have hcutoff :=
      slicedDetection_kernel_cutoff_bound s Cdetect
        (Fintype.card (LayerSamplerVariables G I n B)) G hDetect.1 hDetect.1 hAlog.1 hα
    exact ⟨slicedDetectionGain_lower s Cdetect _ hα, hcutoff,
      allocatedAffineLength_kernel_ready hm hD.1 hPscale0 hPrho.1 hPk.1
        htarget.1 hF hTmod.1 hcutoff hlengthS⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def DetectedCanonicalLateToleranceFreeTrimPreparedStatement (m s : ℕ)
    (Pdetect : Polynomial ℕ) : Prop :=
    let Cdetect := sampledSupportedSlicedDetectionConstant s Pdetect
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)
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
      (∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
        ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩)) →
      (∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
        ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩)) →
      (s + 1) * (s + 3) ≤ Fintype.card G →
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
      ∀ {u P : ℝ}, 0 ≤ u → Bstruct + u ≤ P →
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
      let Qearly := (P + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
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
      let master := budget + Pphysical + Pearly + gainLog + 32
      pRadius ≤ budget ∧ (∀ j, T j ≤ Real.exp budget) ∧
      2 * (siteRadius : ℝ) ≤ Real.exp budget ∧ radiusBudget ≤ Pearly ∧
      P ≤ Pearly ∧ Pearly ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
      aDetect ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧ Tmod ∈ Set.Icc 0 budget ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp budget ∧
      ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := min t (Real.exp (-Qσ))
      let Pscale := pRadius + Ptail + Qσ
      let lengthLog := allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod
      let Pseed := allocatedScaleLog (D + Pscale + lengthLog + 1)
      0 < σ ∧ σ ≤ t ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ Pscale ∈ Set.Icc 0 (2 * budget + Qσ) ∧
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ},
        1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
          Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp
            (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          (∀ lateTarget : ℝ, gainLog + 32 ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget +
              (1 + Pseed ^ 2) * Pmin + Pscale
            let resources := preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m s) (s + 1) master Plate
            resources.nativeBudget = (preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m s) (s + 1) master master).nativeBudget ∧
            (∀ (selection : Fin (s + 1) ↪ G) (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < σ)
              (stride N : Fin nX → ℕ)
              (Q : Fin m → Type) [∀ j, Fintype (Q j)]
              (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
              (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
              (_bW : ∀ j, Module.Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
              [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
              (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
                (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
              [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
              [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
              [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
              [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
              [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
              [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
              [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]
              (Vtail : Fin m → ℝ≥0) (α τfree : ℝ),
              Real.exp (-aDetect) ≤ α → α ≤ 1 →
              PreparedModularGeneralDirectDetectionFreeTrimPreparedInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
                (hb := hb) (o := o) Bstruct Qstride master Plate gainLog Pphysical lateTarget)) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1)) ∧
            (scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value

theorem exists_detected_canonical_late_tolerance_free_trim_prepared (m s : ℕ)
    (Pdetect : Polynomial ℕ) :
    DetectedCanonicalLateToleranceFreeTrimPreparedStatement m s Pdetect := by
  unfold DetectedCanonicalLateToleranceFreeTrimPreparedStatement
  intro Cdetect Aearly
  obtain ⟨C, hC, hearly⟩ := exists_detected_canonical_early_radius_late_tolerance_source m s Cdetect
  refine ⟨C, hC, ?_⟩
  intro G _ _ I _ n B _ _ Bstruct pnum pSlice Qstride nX hm hs hB hnum
    hvars hI hn hblocks hpSlice hQstride hnX hBa hBi hcapacity
    A radiusBudget rowSets T siteRadius D
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hsource⟩ :=
    hearly (G := G) B hm hs hB hnum hvars hI hn hblocks hpSlice hQstride hnX
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro u P hu hmaster Pearly pModel pDetect aDetect gainLog Pk Qearly Pphysical Eextra target
    F Tmod δ E η Prho Ptail K budget master
  have hBP : Bstruct ≤ P := (le_add_of_nonneg_right hu).trans hmaster
  have hP : 0 ≤ P := hB.trans hBP
  have huP : u ≤ P := (le_add_of_nonneg_left hB).trans hmaster
  obtain ⟨hPQ, hEarlyQ, _, _, _, _, hGainQ, hPkQ⟩ :=
    (Classical.choose_spec (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)).2
      (G := G) B hm hs hP ⟨hnum.1, hnum.2.trans hBP⟩ hvars hI hn hblocks
      ⟨hpSlice.1, hpSlice.2.trans hBP⟩ ⟨hu, huP⟩
      ⟨hQstride.1, hQstride.2.trans hBP⟩ (hnX.trans hBP)
  have hQearly0 : 0 ≤ Qearly := hP.trans hPQ
  have hPhysical0 : 0 ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPkQ.1, hQstride.1,
      Nat.cast_nonneg (α := ℝ) nX, Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hExtra : 0 ≤ Eextra := by
    have herror := coefficientErrorSpatialLog_nonneg hPhysical0
    dsimp only [Eextra]
    linarith only [herror]
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      t, ht, htone, htPtail, htbudget, htolerances⟩ := hsource hu hmaster hExtra
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    t, ht, htone, htPtail, htbudget, ?_⟩
  intro Qσ hQσ σ Pscale lengthLog Pseed
  obtain ⟨hσ, hσt, hσexp, hσinv, hScaleBound, hsamplers⟩ := htolerances hQσ
  refine ⟨hσ, hσt, hσexp, hσinv, hScaleBound, ?_⟩
  intro Lmin Wscale Qw Pmin hWscale hQw hWexp hPmin hLmin J _ U basis
  obtain ⟨S, hPkScale, hFloor, hSWitness, hgap, ⟨geometry⟩, hgainKernel⟩ :=
    hsamplers Lmin hWscale hQw hWexp hPmin hLmin U basis
  refine ⟨S, hPkScale, hFloor, hSWitness, hgap, ?_, hgainKernel⟩
  intro lateTarget hCoarseLower Plate resources
  refine ⟨rfl, ?_⟩
  intro selection hRpos hσpos stride N Q _ hb o bW _ ν _ _ _ _ _ μ
    _ _ _ _ _ μrows _ _ _ _ Vtail α τfree hαlower hαone
    hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff hτfree hτfreeInv hτfreeHalf hτfreeDim
  have hGeometry0 : 0 ≤ budget := hModel.1.trans hModel.2
  have hEarly0 : 0 ≤ Pearly := hP.trans hPEarly
  have hGeometryMaster : budget ≤ master := by
    dsimp only [master]
    linarith only [hPhysical0, hEarly0, hgain.1]
  have hPhysicalMaster : Pphysical ∈ Set.Icc 0 master := by
    refine ⟨hPhysical0, ?_⟩
    dsimp only [master]
    linarith only [hGeometry0, hEarly0, hgain.1]
  have hMaster : 0 ≤ master := hGeometry0.trans hGeometryMaster
  have hCoarseMaster : gainLog + 32 ≤ master := by
    dsimp only [master]
    linarith only [hGeometry0, hPhysical0, hEarly0]
  have hLateTarget0 : 0 ≤ lateTarget := by
    linarith only [hgain.1, hCoarseLower]
  have hF : 0 ≤ F := by
    change 0 ≤ pDetect + 2
    linarith only [hDetect.1]
  have hLength0 : 0 ≤ lengthLog :=
    (allocatedAffineLengthLog_bounds m hD.1 hScaleBound.1 hPrho.1 hPk.1
      htarget.1 hF hTmod.1).2.2.1
  have hSeedInput : 0 ≤ D + Pscale + lengthLog + 1 := by
    linarith only [hD.1, hScaleBound.1, hLength0]
  have hSeed0 : 0 ≤ Pseed := allocatedScaleLog_nonneg hSeedInput
  obtain ⟨hBase0, hLateBase, hWitnessBase, hCoarseBase, hXiBase⟩ :=
    preparedModularGeneralDetectorLateMaster_bounds hMaster hSeed0 hQw hPhysical0 hLateTarget0
  have hFloorCost : 0 ≤ (1 + Pseed ^ 2) * Pmin := by positivity
  have hBaseLate : preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget ≤ Plate := by
    dsimp only [Plate]
    linarith only [hFloorCost, hScaleBound.1]
  have hLate := hLateBase.trans hBaseLate
  have hWitnessLate : allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin ≤ Plate := by
    dsimp only [Plate]
    linarith only [hWitnessBase, hScaleBound.1]
  have hCoarseLate := hCoarseBase.trans hBaseLate
  have hXiLate := hXiBase.trans hBaseLate
  have hScaleLate : Pscale ≤ Plate := by
    dsimp only [Plate]
    linarith only [hBase0, hFloorCost]
  have liftMaster {x : ℝ} (hx : x ∈ Set.Icc 0 budget) : x ∈ Set.Icc 0 master :=
    ⟨hx.1, hx.2.trans hGeometryMaster⟩
  have hModelMaster := liftMaster hModel
  have hDetectMaster := liftMaster hDetect
  have hTargetMaster := liftMaster htarget
  have hDMaster := liftMaster hD
  have hGainMaster := liftMaster hgain
  have hPkMaster := liftMaster hPk
  have hPrhoMaster := liftMaster hPrho
  have hpRadiusMaster := hpRadiusBudget.trans hGeometryMaster
  have hSLate := hSWitness.trans (Real.exp_le_exp.mpr hWitnessLate)
  have hPMaster : P ≤ master := hPEarly.trans (hEarlyBudget.trans hGeometryMaster)
  have hBMaster := hBP.trans hPMaster
  have hExpMaster : Real.exp Bstruct ≤ Real.exp master := Real.exp_le_exp.mpr hBMaster
  obtain ⟨_, hSliceModel, _, hcountModel⟩ := detectedCanonicalEarlyRadiusModel_bounds
    (Fintype.card (LayerSamplerVariables G I n B)) hEarly0 hpSlice.1
    (hvars.trans (hnum.2.trans (hBP.trans hPEarly)))
  have hMk := (hgainKernel α hαlower).2
  have hMkPk : (allocatedDetectedKernelCutoff s G
      (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect pDetect α : ℝ) ≤ Real.exp Pk := hMk.1
  have hMkP := hMkPk.trans (Real.exp_le_exp.mpr hPkScale)
  have hKMaster : (Real.toNNReal (Real.exp pRadius) : ℝ) ≤ Real.exp master := by
    rw [Real.coe_toNNReal (Real.exp pRadius) (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr hpRadiusMaster
  have hQPhysical : Qearly ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hPk.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hmPhysical : ((m + 1 : ℕ) : ℝ) ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPk.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX]
  have hDimPhysical : ((s + 2 : ℕ) : ℝ) ≤ Pphysical := by
    have hsm : (s : ℝ) ≤ m := Nat.cast_le.mpr hs
    dsimp only [Pphysical]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    linarith only [hQearly0, hPk.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX, hsm]
  have hXPhysical : (nX : ℝ) ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPk.1, hQstride.1, Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hPkPhysical : Pk ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hQstride.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hQstridePhysical : Qstride ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPk.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hvarsPhysical : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical :=
    hvars.trans (hnum.2.trans (hBP.trans (hPQ.trans hQPhysical)))
  have hprecision : gainLog + 32 + coefficientErrorSpatialLog Pphysical + 8 ≤ target := by
    dsimp only [target, Eextra]
    linarith only
  intro r W ξn hW cells poly hp hmem Rrank hNlarge hrank hRankLarge V
    hcells bases hξn Z
  have hτInvMaster : τfree⁻¹ ≤ Real.exp master :=
    hτfreeInv.trans (Real.exp_le_exp.mpr hPhysicalMaster.2)
  have hξone := preparedModularCanonicalDetector_narrow_width_le_one (Fin nX)
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
    (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
      Pdetect pDetect pDetect α) Pphysical lateTarget
  have hξInvLate : ξn⁻¹ ≤ Real.exp Plate :=
    (preparedModularDetector_narrow_width B selection hPhysical0 hLateTarget0
      (hMkPk.trans (Real.exp_le_exp.mpr hPkPhysical)) hDimPhysical hvarsPhysical hXPhysical).2.trans
      (Real.exp_le_exp.mpr hXiLate)
  obtain ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin⟩ :=
    preparedModularGeneralDetector_late_positive_bounds B U basis S hb o μ ν hRpos hσpos
      (fun _ => hσt.trans htone) Cforward Vtail hforward hVactual Cchart hCchart hchart
      (geometry.hbudgets Cchart hCchart hCchartBound).1 hMaster hLate geometry.hdimensions
      hDMaster.2 (hnX.trans hBMaster)
      (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr hpRadiusMaster))
      (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr hScaleLate)) hSLate
      (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster)
      poly hp hmem stride hstride
      (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr (hQstride.2.trans hBMaster)))
      hτfree hτInvMaster hτfreeHalf hτfreeDim hξn hξone hξInvLate
      N hrank cells hcells hNlarge hRankLarge
  let : ∀ i, NeZero (N i) := fun i => ⟨(hNpos i).ne'⟩
  have consumer := preparedModularGeneralDirectDetectionFreeTrimInterface_of_geometry
    (B := B) (U := U) (basis := basis) (hR := hRpos) (hσ := hσpos) (S := S) (P := Pscale)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν) (μrows := μrows)
    hs Bstruct D target Pk Prho Qstride master Plate gainLog Pphysical lateTarget
    (Real.toNNReal (Real.exp pRadius)) geometry
  have completed := consumer hLate hMaster hDMaster.2 hPkMaster
    ⟨hQstride.1, hQstride.2.trans hBMaster⟩ hDetectMaster (hnX.trans hBMaster)
    (fun j => (hR j).2.1)
    (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr hpRadiusMaster))
    (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr hScaleLate))
    hSLate hKMaster (hcutoff.trans hExpMaster) hMkP hMkPk hstride hstrideBound
    Cchart hCchart hCchartBound hchart Cforward hforward
    (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster) hVactual hBa hBi
    ⟨hu, huP.trans hPMaster⟩ hModelMaster hSliceModel hcountModel hαlower hαone
    hPrhoMaster hTargetMaster hGainMaster hCoarseMaster hCoarseLower hCoarseLate hPhysicalMaster
    hmPhysical hDimPhysical hvarsPhysical hXPhysical hPkPhysical hQstridePhysical
    (le_refl _) hprecision hXiLate hτfree hτfreeInv
  refine ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path pathLaw sides Sites e Tests _ Ldetect _ _ dims _ _ _ _
    Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount hcomplexity hnorm budget'
  exact completed cells poly hp hmem hNlarge hrank hRankLarge hcells hbases hmass
    hnormalizer.2.2.1 Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount
    hcomplexity hnorm hcapacity hMk.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def PreparedLateToleranceFreeTrimSourceStatement (m : ℕ) (Pdetect : Polynomial ℕ) : Prop :=
    let Cdetect := sampledSupportedSlicedDetectionConstant 0 Pdetect
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {Pstruct pSlice Qstride : ℝ},
      0 < m → 0 ≤ Pstruct → (M : ℝ) ≤ Pstruct →
      pSlice ∈ Set.Icc 0 Pstruct → Qstride ∈ Set.Icc 0 Pstruct → (nX : ℝ) ≤ Pstruct →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Bstruct := (Pstruct + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m)
    let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let radiusBudget := Bstruct + (2 * Bstruct + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let D := allocatedComparisonDimension m pnum
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 radiusBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (0 + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (0 + 1)) *
            ((Fintype.card (Fin (0 + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Bstruct) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (0 + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (0 + 1)) (fun j => (rowSets j : Type)) D ∧
      ∀ {u P : ℝ}, 0 ≤ u → Bstruct + u ≤ P →
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
      let Qearly := (P + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
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
      let master := budget + Pphysical + Pearly + gainLog + 32
      pRadius ≤ budget ∧ (∀ j, T j ≤ Real.exp budget) ∧
      2 * (siteRadius : ℝ) ≤ Real.exp budget ∧ radiusBudget ≤ Pearly ∧
      P ≤ Pearly ∧ Pearly ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
      aDetect ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧ Tmod ∈ Set.Icc 0 budget ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp budget ∧
      ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := min t (Real.exp (-Qσ))
      let Pscale := pRadius + Ptail + Qσ
      let lengthLog := allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod
      let Pseed := allocatedScaleLog (D + Pscale + lengthLog + 1)
      0 < σ ∧ σ ≤ t ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ Pscale ∈ Set.Icc 0 (2 * budget + Qσ) ∧
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ},
        1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
          Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp
            (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          (∀ lateTarget : ℝ, gainLog + 32 ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget +
              (1 + Pseed ^ 2) * Pmin + Pscale
            let resources := preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master Plate
            resources.nativeBudget = (preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master master).nativeBudget ∧
            (∀ (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < σ)
              (stride N : Fin nX → ℕ)
              (Q : Fin m → Type) [∀ j, Fintype (Q j)]
              (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
              (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
              (_bW : ∀ j, Module.Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
              [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
              (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
                (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
              [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
              [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
              [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
              [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
              [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
              [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
              [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
              (Vtail : Fin m → ℝ≥0) (α τfree : ℝ),
              Real.exp (-aDetect) ≤ α → α ≤ 1 →
              PreparedModularGeneralDirectDetectionFreeTrimPreparedInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
                (hb := hb) (o := o) Bstruct Qstride master Plate gainLog Pphysical lateTarget)) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
            (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value

theorem exists_prepared_late_tolerance_free_trim_source (m : ℕ) (Pdetect : Polynomial ℕ) :
    PreparedLateToleranceFreeTrimSourceStatement m Pdetect := by
  unfold PreparedLateToleranceFreeTrimSourceStatement
  intro Cdetect Aearly Aalloc
  have hactual := exists_detected_canonical_late_tolerance_free_trim_prepared m 0 Pdetect
  unfold DetectedCanonicalLateToleranceFreeTrimPreparedStatement at hactual
  obtain ⟨C, hC, hsource⟩ := hactual
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord Pstruct pSlice Qstride hm hPstruct hM hpSlice hQstride hnX
    Jalloc pnum Bstruct G I n B selection A radiusBudget rowSets T siteRadius D
  obtain ⟨hStruct, _, hnum, _⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetectorAllocationBudget m)).2
      hPstruct hM hnX
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hCoord
  have hblocks (a : LayerSamplerAxis I n) :
      (boundedBooleanJetRows (Fin (0 + 1)) (a.1.val + 1)).card ≤ Fintype.card (B a) := by
    calc
      _ = Fintype.card (BoundedBooleanJet (Fin (0 + 1)) (a.1.val + 1)) :=
        (Fintype.card_coe _).symm.trans (Fintype.card_congr (boundedBooleanJetRowsEquiv _ _))
      _ ≤ _ := enlargedPreparedCommonSamplerBlock_jets L Jalloc 0 (Nat.zero_le m) a
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hlate⟩ :=
    hsource (G := G) B hm (Nat.zero_le m) (hPstruct.trans hStruct) hnum
      (Nat.cast_le.mpr hvars) (fun j => Nat.cast_le.mpr (hI j))
      (fun j => Nat.cast_le.mpr (hn j)) hblocks
      ⟨hpSlice.1, hpSlice.2.trans hStruct⟩ ⟨hQstride.1, hQstride.2.trans hStruct⟩
      (hnX.trans hStruct)
      (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate L Jalloc 0 (Nat.zero_le m) ⟨j, Sum.inr i⟩)
      (fun j i => enlargedPreparedCommonSamplerBlock_uniform L Jalloc 0 (Nat.zero_le m) ⟨j, Sum.inr i⟩)
      (enlargedPreparedCommonKernel_analytic_capacity m Jalloc 0 (Nat.zero_le m))
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro u P hu hmaster Pearly pModel pDetect aDetect gainLog Pk Qearly Pphysical Eextra target
    F Tmod δ E η Prho Ptail K budget master
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      t, ht, htone, htPtail, htbudget, htolerances⟩ := hlate hu hmaster
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    t, ht, htone, htPtail, htbudget, ?_⟩
  intro Qσ hQσ σ Pscale lengthLog Pseed
  obtain ⟨hσ, hσt, hσexp, hσinv, hScaleBound, hsamplers⟩ := htolerances hQσ
  refine ⟨hσ, hσt, hσexp, hσinv, hScaleBound, ?_⟩
  intro Lmin Wscale Qw Pmin hWscale hQw hWexp hPmin hLmin J _ U basis
  obtain ⟨S, hPkScale, hFloor, hSWitness, hgap, hdetector, hgainKernel⟩ :=
    hsamplers Lmin hWscale hQw hWexp hPmin hLmin U basis
  refine ⟨S, hPkScale, hFloor, hSWitness, hgap, ?_, hgainKernel⟩
  intro lateTarget hCoarseLower Plate resources
  obtain ⟨hnative, hprepared⟩ := hdetector lateTarget hCoarseLower
  exact ⟨hnative, hprepared selection⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

private theorem centeredSource_physical_bounds {Qearly Pk Qstride : ℝ} (nX m : ℕ)
    (hQ : 0 ≤ Qearly) (hPk : 0 ≤ Pk) (hs : 0 ≤ Qstride) :
    let physical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
    0 ≤ physical ∧ Pk ≤ physical ∧ (nX : ℝ) ≤ physical ∧
      (2 : ℝ) ≤ physical ∧ Qearly ≤ physical := by
  intro physical
  dsimp only [physical]
  have hn : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ (m + 1 : ℕ) := Nat.cast_nonneg _
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

private theorem centeredSource_master_bounds {budget physical early gain : ℝ}
    (hb : 0 ≤ budget) (hp : 0 ≤ physical) (he : 0 ≤ early) (hg : 0 ≤ gain) :
    let master := budget + physical + early + gain + 32
    budget ≤ master ∧ physical ≤ master ∧ 0 ≤ master := by
  dsimp only
  exact ⟨by linarith, by linarith, by linarith⟩

private theorem centeredSource_late_bounds {master seed Qw physical target Pmin scale : ℝ}
    (hm : 0 ≤ master) (hs : 0 ≤ seed) (hw : 0 ≤ Qw) (hp : 0 ≤ physical)
    (ht : 0 ≤ target) (hmin : 0 ≤ Pmin) (hscale : 0 ≤ scale) :
    let base := preparedModularGeneralDetectorLateMaster master seed Qw physical target
    let late := base + (1 + seed ^ 2) * Pmin + scale
    master ≤ late ∧
      allocatedWitnessScaleLog seed Qw + (1 + seed ^ 2) * Pmin ≤ late ∧
      scale ≤ late ∧
      2 * (spatialPrimitiveEnvelope physical target 0 +
        spatialTupleToleranceLog (spatialPrimitiveEnvelope physical target 0)) + 4 ≤ late := by
  intro base late
  obtain ⟨hb, hm', hw', _, hξ⟩ :=
    preparedModularGeneralDetectorLateMaster_bounds hm hs hw hp ht
  have hc : 0 ≤ (1 + seed ^ 2) * Pmin := mul_nonneg (by positivity) hmin
  dsimp only [late]
  exact ⟨by linarith only [hm', hc, hscale],
    by linarith only [hw', hscale], by linarith only [hb, hc],
    by linarith only [hξ, hc, hscale]⟩

def PreparedLateToleranceCenteredSourceStatement (m : ℕ) (Pdetect : Polynomial ℕ) : Prop :=
    let Cdetect := sampledSupportedSlicedDetectionConstant 0 Pdetect
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {Pstruct pSlice Qstride : ℝ},
      0 < m → 0 ≤ Pstruct → (M : ℝ) ≤ Pstruct →
      pSlice ∈ Set.Icc 0 Pstruct → Qstride ∈ Set.Icc 0 Pstruct → (nX : ℝ) ≤ Pstruct →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Bstruct := (Pstruct + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m)
    let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let radiusBudget := Bstruct + (2 * Bstruct + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let D := allocatedComparisonDimension m pnum
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 radiusBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (0 + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (0 + 1)) *
            ((Fintype.card (Fin (0 + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Bstruct) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (0 + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (0 + 1)) (fun j => (rowSets j : Type)) D ∧
      ∀ {u P : ℝ}, 0 ≤ u → Bstruct + u ≤ P →
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
      let Qearly := (P + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
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
      let master := budget + Pphysical + Pearly + gainLog + 32
      pRadius ≤ budget ∧ (∀ j, T j ≤ Real.exp budget) ∧
      2 * (siteRadius : ℝ) ≤ Real.exp budget ∧ radiusBudget ≤ Pearly ∧
      P ≤ Pearly ∧ Pearly ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
      aDetect ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧ Tmod ∈ Set.Icc 0 budget ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp budget ∧
      ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := min t (Real.exp (-Qσ))
      let Pscale := pRadius + Ptail + Qσ
      let lengthLog := allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod
      let Pseed := allocatedScaleLog (D + Pscale + lengthLog + 1)
      0 < σ ∧ σ ≤ t ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ Pscale ∈ Set.Icc 0 (2 * budget + Qσ) ∧
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ},
        1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
          Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp
            (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          (∀ lateTarget : ℝ, gainLog + 32 ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget +
              (1 + Pseed ^ 2) * Pmin + Pscale
            let resources := preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master Plate
            resources.nativeBudget = (preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master master).nativeBudget ∧
            (∀ (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < σ)
              (stride N : Fin nX → ℕ)
              (Q : Fin m → Type) [∀ j, Fintype (Q j)]
              (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
              (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
              (_bW : ∀ j, Module.Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
              [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
              (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
                (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
              [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
              [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
              [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
              [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
              [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
              [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
              [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
              (Vtail : Fin m → ℝ≥0) (α τfree : ℝ),
              Real.exp (-aDetect) ≤ α / 2 → α ≤ 1 →
              PreparedCenteredModelMarginalRadiusInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
                (hb := hb) (o := o) (μ := μ) Bstruct Qstride master Plate gainLog Pphysical lateTarget)) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
            (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value

theorem exists_prepared_late_tolerance_centered_source (m : ℕ) (Pdetect : Polynomial ℕ) :
    PreparedLateToleranceCenteredSourceStatement m Pdetect := by
  unfold PreparedLateToleranceCenteredSourceStatement
  intro Cdetect Aearly Aalloc
  have hactual := exists_prepared_late_tolerance_free_trim_source m Pdetect
  unfold PreparedLateToleranceFreeTrimSourceStatement at hactual
  obtain ⟨C, hC, hsource⟩ := hactual
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord Pstruct pSlice Qstride hm hPstruct hM hpSlice hQstride hnX
    Jalloc pnum Bstruct G I n B selection A radiusBudget rowSets T siteRadius D
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hlate⟩ :=
    hsource L hCoord hm hPstruct hM hpSlice hQstride hnX
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro u P hu hmaster Pearly pModel pDetect aDetect gainLog Pk Qearly Pphysical Eextra target
    F Tmod δ E η Prho Ptail K budget master
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      t, ht, htone, htPtail, htbudget, htolerances⟩ := hlate hu hmaster
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    t, ht, htone, htPtail, htbudget, ?_⟩
  intro Qσ hQσ σ Pscale lengthLog Pseed
  obtain ⟨hσ, hσt, hσexp, hσinv, hScaleBound, hsamplers⟩ := htolerances hQσ
  refine ⟨hσ, hσt, hσexp, hσinv, hScaleBound, ?_⟩
  intro Lmin Wscale Qw Pmin hWscale hQw hWexp hPmin hLmin J _ U basis
  obtain ⟨S, hPkScale, hFloor, hSWitness, hgap, hdetector, hgainKernel⟩ :=
    hsamplers Lmin hWscale hQw hWexp hPmin hLmin U basis
  refine ⟨S, hPkScale, hFloor, hSWitness, hgap, ?_, hgainKernel⟩
  intro lateTarget hCoarseLower Plate resources
  obtain ⟨hnative, hprepared⟩ := hdetector lateTarget hCoarseLower
  refine ⟨hnative, ?_⟩
  intro hRpos hσpos stride N Q _ hb o bW _ ν _ _ _ _ _ μ
    _ _ _ _ _ μrows _ _ _ _ Vtail α τfree hαlower hαone
  have hDirect := hprepared hRpos hσpos stride N Q hb o bW ν μ μrows Vtail
    (α / 2) τfree hαlower (by linarith only [hαone])
  obtain ⟨hStruct, _, hnum, _⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetectorAllocationBudget m)).2
      hPstruct hM hnX
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hCoord
  have hB : 0 ≤ Bstruct := hPstruct.trans hStruct
  have hBP : Bstruct ≤ P := (le_add_of_nonneg_right hu).trans hmaster
  have hP : 0 ≤ P := hB.trans hBP
  have hQearly : 0 ≤ Qearly := by dsimp only [Qearly]; positivity
  obtain ⟨hPhysical0, hPkPhysical, hXPhysical, hDimPhysical, hQPhysical⟩ :=
    centeredSource_physical_bounds nX m hQearly hPk.1 hQstride.1
  have hGeometry0 : 0 ≤ budget := hModel.1.trans hModel.2
  have hEarly0 : 0 ≤ Pearly := hP.trans hPEarly
  obtain ⟨hGeometryMaster, hPhysicalMaster, hMaster⟩ :=
    centeredSource_master_bounds hGeometry0 hPhysical0 hEarly0 hgain.1
  have hPMaster : P ≤ master := hPEarly.trans (hEarlyBudget.trans hGeometryMaster)
  have hBMaster := hBP.trans hPMaster
  have hLateTarget0 : 0 ≤ lateTarget := by linarith only [hgain.1, hCoarseLower]
  have hF : 0 ≤ F := by change 0 ≤ pDetect + 2; linarith only [hDetect.1]
  have hLength0 : 0 ≤ lengthLog :=
    (allocatedAffineLengthLog_bounds m hD.1 hScaleBound.1 hPrho.1 hPk.1
      htarget.1 hF hTmod.1).2.2.1
  have hSeedInput : 0 ≤ D + Pscale + lengthLog + 1 := by
    linarith only [hD.1, hScaleBound.1, hLength0]
  have hSeed0 : 0 ≤ Pseed := allocatedScaleLog_nonneg hSeedInput
  obtain ⟨hLate, hWitnessLate, hScaleLate, hXiLate⟩ :=
    centeredSource_late_bounds hMaster hSeed0 hQw hPhysical0 hLateTarget0 hPmin hScaleBound.1
  have hSLate := hSWitness.trans (Real.exp_le_exp.mpr hWitnessLate)
  have hMkPk : (allocatedDetectedKernelCutoff 0 G
      (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect pDetect (α / 2) : ℝ) ≤ Real.exp Pk :=
    (hgainKernel (α / 2) hαlower).2.1
  have hblocks (a : LayerSamplerAxis I n) :
      (boundedBooleanJetRows (Fin (0 + 1)) (a.1.val + 1)).card ≤ Fintype.card (B a) := by
    calc
      _ = Fintype.card (BoundedBooleanJet (Fin (0 + 1)) (a.1.val + 1)) :=
        (Fintype.card_coe _).symm.trans (Fintype.card_congr (boundedBooleanJetRowsEquiv _ _))
      _ ≤ _ := enlargedPreparedCommonSamplerBlock_jets L Jalloc 0 (Nat.zero_le m) a
  have hPearly :=
    (Classical.choose_spec (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)).2
      (G := G) B hm (Nat.zero_le m) hP ⟨hnum.1, hnum.2.trans hBP⟩
      (Nat.cast_le.mpr hvars) (fun j => Nat.cast_le.mpr (hI j))
      (fun j => Nat.cast_le.mpr (hn j)) hblocks
      ⟨hpSlice.1, hpSlice.2.trans (hStruct.trans hBP)⟩
      ⟨hu, (le_add_of_nonneg_left hB).trans hmaster⟩
      ⟨hQstride.1, hQstride.2.trans (hStruct.trans hBP)⟩ (hnX.trans (hStruct.trans hBP))
  have hvarsPhysical : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical :=
    (Nat.cast_le.mpr hvars).trans (hnum.2.trans (hBP.trans (hPearly.1.trans hQPhysical)))
  have hξLate :=
    (preparedModularDetector_narrow_width B selection hPhysical0 hLateTarget0
      (hMkPk.trans (Real.exp_le_exp.mpr hPkPhysical)) hDimPhysical hvarsPhysical hXPhysical).2.trans
      (Real.exp_le_exp.mpr hXiLate)
  apply preparedCenteredModelMarginalRadiusInterface_of_projection
    B U basis hRpos hσpos S selection stride N Pdetect u pModel pSlice Vtail α τfree hb o μ
    Bstruct Qstride master Plate gainLog Pphysical lateTarget
  · exact preparedCenteredModelMarginalProjectionData_of_direct
      B U basis hRpos hσpos S selection stride N Pdetect u pModel pSlice Vtail α τfree hb o ν μ
      Bstruct Qstride master Plate gainLog Pphysical lateTarget hDirect hMaster hLate
      hdimensions (hD.2.trans hGeometryMaster) (hXPhysical.trans hPhysicalMaster)
      hBMaster (hQstride.2.trans (hStruct.trans hBMaster)) hPhysicalMaster
      (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr (hpRadiusBudget.trans hGeometryMaster)))
      (fun _ => hσinv.trans (Real.exp_le_exp.mpr hScaleLate)) hSLate
      (fun _ => hσt.trans htone) hξLate
  · intro Cchart hCchart hCchartBound
    exact (hsmall Cchart hCchart hCchartBound).1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def PreparedLateToleranceCertifiedSourceStatement (m : ℕ) (Pdetect : Polynomial ℕ) : Prop :=
    let Cdetect := sampledSupportedSlicedDetectionConstant 0 Pdetect
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {Pstruct pSlice Qstride : ℝ},
      0 < m → 0 ≤ Pstruct → (M : ℝ) ≤ Pstruct →
      pSlice ∈ Set.Icc 0 Pstruct → Qstride ∈ Set.Icc 0 Pstruct → (nX : ℝ) ≤ Pstruct →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Bstruct := (Pstruct + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m)
    let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let radiusBudget := Bstruct + (2 * Bstruct + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let D := allocatedComparisonDimension m pnum
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 radiusBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (0 + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (0 + 1)) *
            ((Fintype.card (Fin (0 + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Bstruct) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (0 + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (0 + 1)) (fun j => (rowSets j : Type)) D ∧
      ∀ {u P : ℝ}, 0 ≤ u → Bstruct + u ≤ P →
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
      let Qearly := (P + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
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
      let master := budget + Pphysical + Pearly + gainLog + 32
      pRadius ≤ budget ∧ (∀ j, T j ≤ Real.exp budget) ∧
      2 * (siteRadius : ℝ) ≤ Real.exp budget ∧ radiusBudget ≤ Pearly ∧
      P ≤ Pearly ∧ Pearly ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
      aDetect ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧ Tmod ∈ Set.Icc 0 budget ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp budget ∧
      ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := min t (Real.exp (-Qσ))
      let Pscale := pRadius + Ptail + Qσ
      let lengthLog := allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod
      let Pseed := allocatedScaleLog (D + Pscale + lengthLog + 1)
      0 < σ ∧ σ ≤ t ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ Pscale ∈ Set.Icc 0 (2 * budget + Qσ) ∧
      ∀ (Lmin : ℕ) {Pmin Elog Vlog : ℝ} (Qbad : ℕ),
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
        0 ≤ Elog → 0 ≤ Vlog → 1 ≤ Qbad → (Qbad : ℝ) ≤ Real.exp Vlog →
      let W := physicalBadProductGap (Jalloc * (nX + m * M)) Elog Vlog Qbad
      let Qw := 2 * Bstruct + 2 * Vlog + 5 * Elog + 24
      let J := fun j : Fin m => (L j).Coord
      let Pbase := Bstruct + Pscale + pRadius
      let B0 := 1 + Pbase + Pseed + Qw + Pmin + Elog + Vlog
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
          Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp
            (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          (∀ Bcert : ℝ, B0 ≤ Bcert →
            PreparedCertifiedSameScaleBadProductInterface L U basis S Bcert Elog Vlog Qbad) ∧
          (∀ lateTarget : ℝ, gainLog + 32 ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget +
              (1 + Pseed ^ 2) * Pmin + Pscale
            let resources := preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master Plate
            resources.nativeBudget = (preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master master).nativeBudget ∧
            (∀ (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < σ)
              (stride N : Fin nX → ℕ)
              (Q : Fin m → Type) [∀ j, Fintype (Q j)]
              (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
              (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
              (_bW : ∀ j, Module.Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
              [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
              (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
                (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
              [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
              [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
              [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
              [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
              [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
              [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
              [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
              (Vtail : Fin m → ℝ≥0) (α τfree : ℝ),
              Real.exp (-aDetect) ≤ α / 2 → α ≤ 1 →
              PreparedCenteredModelMarginalRadiusInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
                (hb := hb) (o := o) (μ := μ) Bstruct Qstride master Plate gainLog Pphysical lateTarget)) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
            (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value

theorem exists_prepared_late_tolerance_certified_source (m : ℕ) (Pdetect : Polynomial ℕ) :
    PreparedLateToleranceCertifiedSourceStatement m Pdetect := by
  classical
  unfold PreparedLateToleranceCertifiedSourceStatement
  intro Cdetect Aearly Aalloc
  have hactual := exists_prepared_late_tolerance_centered_source m Pdetect
  unfold PreparedLateToleranceCenteredSourceStatement at hactual
  obtain ⟨C, hC, hsource⟩ := hactual
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord Pstruct pSlice Qstride hm hPstruct hM hpSlice hQstride hnX
    Jalloc pnum Bstruct G I n B selection A radiusBudget rowSets T siteRadius D
  obtain ⟨hStruct, _, hnum, _⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetectorAllocationBudget m)).2
      hPstruct hM hnX
  have hBstruct : 0 ≤ Bstruct := hPstruct.trans hStruct
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hlate⟩ :=
    hsource L hCoord hm hPstruct hM hpSlice hQstride hnX
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro u P hu hmaster Pearly pModel pDetect aDetect gainLog Pk Qearly Pphysical Eextra target
    F Tmod δ E η Prho Ptail K budget master
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      t, ht, htone, htPtail, htbudget, htolerances⟩ := hlate hu hmaster
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    t, ht, htone, htPtail, htbudget, ?_⟩
  intro Qσ hQσ σ Pscale lengthLog Pseed
  obtain ⟨hσ, hσt, hσexp, hσinv, hScaleBound, hsamplers⟩ := htolerances hQσ
  refine ⟨hσ, hσt, hσexp, hσinv, hScaleBound, ?_⟩
  intro Lmin Pmin Elog Vlog Qbad hPmin hLmin hElog hVlog hQbad hQexp W Qw J Pbase B0 U basis
  have hQw : 0 ≤ Qw := by dsimp only [Qw]; linarith only [hBstruct, hVlog, hElog]
  obtain ⟨hW, hWexp⟩ := preparedBadProductWitnessGap_bounds m nX M hnum.2
    hElog hVlog Qbad hQbad hQexp
  obtain ⟨S, hPkScale, hFloor, hSWitness, hgap, hdetector, hgainKernel⟩ :=
    hsamplers Lmin hW hQw hWexp hPmin hLmin U basis
  refine ⟨S, hPkScale, hFloor, hSWitness, hgap, ?_, hdetector, hgainKernel⟩
  have hF : 0 ≤ F := by change 0 ≤ pDetect + 2; linarith only [hDetect.1]
  have hLength : 0 ≤ lengthLog :=
    (allocatedAffineLengthLog_bounds m hD.1 hScaleBound.1 hPrho.1 hPk.1
      htarget.1 hF hTmod.1).2.2.1
  have hSeedInput : 0 ≤ D + Pscale + lengthLog + 1 := by
    linarith only [hD.1, hScaleBound.1, hLength]
  have hSeed : 0 ≤ Pseed := allocatedScaleLog_nonneg hSeedInput
  have hcert := preparedCertifiedSameScaleBadProductInterface_of_lateTolerance_larger
    (nX := nX) (M := M) (R := R) (σ := fun _ : Fin m => σ) L U basis S
    (Bstruct := Bstruct) (pRadius := pRadius) (Pscale := Pscale)
    (Elog := Elog) (Vlog := Vlog) (Pseed := Pseed) (Qw := Qw) (Pmin := Pmin) Qbad
    hBstruct hpRadius.1 hScaleBound.1 (hM.trans hStruct) (hnX.trans hStruct)
    (fun j => (hR j).2.2) (fun _ => hσinv)
    hSeed hQw hPmin hElog hVlog hQbad hQexp hm hCoord hSWitness hgap
  exact hcert

end Erdos3.VectorPolynomial

end

end OAI

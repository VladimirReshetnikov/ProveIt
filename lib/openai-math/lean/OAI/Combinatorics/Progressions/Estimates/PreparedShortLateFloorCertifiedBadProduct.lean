import OAI.Combinatorics.Progressions.Estimates.PreparedCenteredShortJointBadProduct

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

def PreparedCertifiedSameScaleBadProductInterface (B Elog Vlog : ℝ) (Q : ℕ) : Prop :=
  let Ps := (B + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m
  ∀ {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp B)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp B) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp B)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {ρ Rs Smax : ℝ}
    (_hρ : 0 < ρ) (_hρPs : 1 / ρ ≤ Real.exp B)
    (stride : Fin nX → ℕ) (_hstride : ∀ x, 0 < stride x)
    (_hSmax : 0 ≤ Smax) (_hSmaxPs : Smax ≤ Real.exp B) (_hstrideMax : ∀ x, ((stride x * ((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℕ) : ℝ) ≤ Smax)
    (H : Fin nX → ℝ)
    (_hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (_hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (_hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) (hwidth : ∀ z, 0 < width z)
    (_hwide : ∀ z, ρ * H z.2 ≤ width z)
    , let Dphysical := fun z : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ =>
      allocatedCoefficientDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
    ∃ read : (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
        AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ,
      (∀ z, allocatedReadNoise (read z) = z) ∧
      (∀ z, Dphysical z ≠ 0 →
        ∀ (primes : Finset ℕ) (hne : ∀ p : primes, NeZero p.val),
          letI := hne
          ∀ (depth : ℕ → ℕ) (q : ℕ) (hq : 0 < q),
            letI : NeZero q := ⟨hq.ne'⟩
            ∀ hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q,
              coefficientDeckChartEvent U bW b hb o q
                (allocatedChartResiduePrimePowerWitness
                  (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value)
                  (modularInitialRankStrength m (nX + m * M) : ℝ) primes depth q hdiv
                  (fun v => (z v : ZMod q)))
                (affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))) ↔
              ∀ p : primes, allocatedActualModulusBad
                (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value)
                (preparedInitialRankSpatialEmbedding (m := m) nX M)
                (preparedInitialRankKernelEmbedding (m := m) nX M)
                (preparedInitialRankPrincipalEmbedding prep nX M
                  (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value))
                (modularInitialRankStrength m (nX + m * M) : ℝ)
                (p.val ^ depth p.val) (read z)) ∧
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 3 * (physicalBadProductAccuracy Elog Vlog) ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      0 < (quantitativeBadPrimeRadius Elog) ∧ ((quantitativeBadPrimeRadius Elog) : ℝ) ≤ Real.exp (Elog + 3) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
          (∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
            (if (∏ x, stride x) ^ 2 *
              (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * (quantitativeBadPrimeRadius Elog)) <
                ∏ p ∈ primes, p ^ largestTestedBadDepth depth
                  (fun p a z => allocatedActualPrimeBad (allocatedGridAxis (I := (PreparedSamplerContinuous prep)) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M)
                    (preparedInitialRankPrincipalEmbedding prep nX M (allocatedGridAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) primes ((modularInitialRankStrength m ((nX + m * M : ℕ)) : ℝ)) p a (read z)) p z
              then (1 : ℝ) else 0)) ≤ Real.exp (-Elog)

theorem preparedCertifiedSameScaleBadProductInterface_of_bounds
    {B Elog Vlog : ℝ} (Q : ℕ) (hB : 1 ≤ B) (hMB : (M : ℝ) ≤ B) (hnXB : (nX : ℝ) ≤ B)
    (hElogB : Elog ∈ Set.Icc 0 B) (hVlogB : Vlog ∈ Set.Icc 0 B)
    (hQ : 1 ≤ Q) (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp B) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp B)
    (hS : (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog B (2 * B + 2 * Vlog + 5 * Elog + 24)))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M)) Elog Vlog Q ≤
          (layerSamplerGapWidth (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j,i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    PreparedCertifiedSameScaleBadProductInterface prep U b S B Elog Vlog Q := by
  unfold PreparedCertifiedSameScaleBadProductInterface
  intro Ps E instE bW hb o C V hC hV hR hσ hσ1
    Cinv hCinv hchart hsmall hAP hCP hVP
    instLattice instCompact instMeasurable instBorel μ instLeft instProbability ν instνLeft instνProb
    poly hp hm ρ Rs Smax hρ hρPs stride hstride
    hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells width hwidth hwide
  let P := (B + preparedBadProductCoefficientExponent m) ^ preparedBadProductCoefficientExponent m
  have hbudget := (exists_preparedBadProductFinalBudget m).choose_spec.choose_spec
  obtain ⟨hP1, hPs1, hBP, hP0P, hprimitive, hPscale, hbudgetP, hframe, hPPS, hWlog, hfreq, hmass⟩ :=
    hbudget.2.2 hB hMB hnXB (show B ∈ Set.Icc 0 B from ⟨zero_le_one.trans hB, le_rfl⟩) hElogB hVlogB
  have hP : 0 ≤ P := zero_le_one.trans hP1
  have hPs : 0 ≤ Ps := zero_le_one.trans hPs1
  have hbudgetPs := hbudgetP.trans hPPS
  have hcounts : (((m + 1) * (enlargedPreparedCommonSamplerDimension m M
        (modularInitialBlockCount m (nX + m * M)) + 1) ^ m +
        enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M)) : ℕ) : ℝ) ≤ P := by
    simpa only [P, preparedBadProductCoefficientExponent, Nat.cast_add] using hprimitive
  exact exists_prepared_certified_physical_bad_product prep U bW b hb o S C V hC hV Elog Vlog Q
    hElogB.1 hVlogB.1 hQ hQexp hmpos hCoord hR hσ hσ1 Cinv hCinv hchart hsmall hP hcounts
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hBP))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hBP))
    (hAP.trans (Real.exp_le_exp.mpr hBP)) (hS.trans (Real.exp_le_exp.mpr hPscale))
    (fun j => (hCP j).trans (Real.exp_le_exp.mpr hBP))
    (fun j => (hVP j).trans (Real.exp_le_exp.mpr hBP)) hbudgetP μ ν poly hp hm
    hPs hframe hbudgetPs hρ (hρPs.trans (Real.exp_le_exp.mpr (hBP.trans hPPS))) stride hstride
    hSmax (hSmaxPs.trans (Real.exp_le_exp.mpr (hBP.trans hPPS))) hstrideMax
    H hsize hrank hRs cells hcells width hwidth hwide hfreq hmass hprincipal hPPS hWlog

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

omit [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))] in

theorem preparedCenteredJoint_badProduct_of_read
    (B0 Elog Vlog : ℝ) (Q : ℕ)
    (hsource : PreparedCertifiedSameScaleBadProductInterface prep U b S B0 Elog Vlog Q)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp B0)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp B0) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp B0)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {ρ Rs Smax : ℝ}
    (hρ : 0 < ρ) (hρPs : 1 / ρ ≤ Real.exp B0)
    (stride : Fin nX → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp B0) (hstrideMax : ∀ x, ((stride x * ((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℕ) : ℝ) ≤ Smax)
    (H : Fin nX → ℝ)
    (hsize : ∀ x, Real.exp ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)

    (center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (read : (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ)
    (hread : ∀ a z, allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center a z ≠ 0 → AllocatedPhysicalRankReadCertificate (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o (allocatedCenteredConditionalPolynomial U poly c a) (allocatedCenteredConditionalPolynomial_mem U poly hm c a) (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) z (read a z)) :
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ _hlocal : ∀ a, 0 < selectedResidueDensityMass stride cells width (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center a),
    ∀ (bases : Finset (Fin nX → ℤ)) (hbases : bases.Nonempty),
      ∃ htotal : 0 < selectedJointDensityMass bases stride cells width (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center),
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
          (selectedJointFiniteLaw bases hbases stride cells width hwidth hZ (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center)
            (allocatedCenteredJointDensity_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) htotal).mean
            (fun az => let a := az.1.val; let z := az.2.val
              if (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius Elog) <
        ∏ p ∈ primes, p ^ largestTestedBadDepth depth
          (fun p d z => allocatedActualPrimeBad (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M)
            (preparedInitialRankPrincipalEmbedding prep nX M (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ) p d (read a z)) p z then (1 : ℝ) else 0) ≤ Real.exp (-Elog) := by
  let density := allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center
  have hconditional (a : Fin nX → ℤ) :=
    hsource bW hb o C V hC hV hR hσ hσ1 Cinv hCinv hchart hsmall hAP hCP hVP μ ν
      (allocatedCenteredConditionalPolynomial U poly c a) (allocatedCenteredConditionalPolynomial_degree U poly c a hp)
      (allocatedCenteredConditionalPolynomial_mem U poly hm c a) hρ hρPs stride hstride hSmax hSmaxPs hstrideMax H hsize
      (fun j => (allocatedCenteredConditionalPolynomial_rank U poly c a hp H Rs j).mpr (hrank j))
      hRs cells hcells width hwidth hwide
  dsimp only at hconditional
  simp_rw [allocatedCenteredConditionalPolynomial_density U poly hm c _ (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) b hb o hR hσ S center hc] at hconditional
  choose hD0 hZ hDpos chosen hnoise hcert hmass hlower hupper hRbad hRbound htail using hconditional
  refine ⟨hZ 0, hDpos, ?_⟩
  intro bases hbases
  have htotal : 0 < selectedJointDensityMass bases stride cells width density := by
    have hbound := selectedJointDensityMass_bounds bases hbases stride cells width density
      (fun a => ⟨hlower a, hupper a⟩)
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hbound.1
  refine ⟨htotal, ?_⟩
  intro primes hprime
  let : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
  intro depth hdepth
  have hmix := selectedJointFiniteLaw_conditional_event_le bases hbases stride cells width hwidth (hZ 0)
    density hD0 htotal hDpos (fun a z =>
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius Elog) <
      ∏ p ∈ primes, p ^ largestTestedBadDepth depth
        (fun p d z => allocatedActualPrimeBad
          (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value)
          (preparedInitialRankSpatialEmbedding (m := m) nX M)
          (preparedInitialRankKernelEmbedding (m := m) nX M)
          (preparedInitialRankPrincipalEmbedding prep nX M
            (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes
          (modularInitialRankStrength m (nX + m * M) : ℝ) p d (read a z)) p z) (ε := Real.exp (-Elog))
  apply (show _ = _ from ?_).trans_le (hmix ?_)
  · congr 1
    funext az
    dsimp only
    split_ifs <;> rfl
  intro a
  have ht := htail a primes hprime depth hdepth
  have heq := selectedResidueDensityPMF_certifiedRead_badProduct_congr
    (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o (allocatedCenteredConditionalPolynomial U poly c a) (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
    (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ)
    stride cells width hwidth (hZ 0) (density a) (hD0 a) (hDpos a)
    (chosen a) (read a) (hcert a) (hread a) primes depth
    ((∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius Elog))
  rw [heq] at ht
  apply le_of_eq_of_le ?_ ht
  apply tsum_congr
  intro z
  congr 1
  split_ifs <;> rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

theorem allocatedWitnessScaleLog_lateFloor_le {Pseed Qw Pmin B E V : ℝ}
    (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hB : Pseed + Pmin ≤ B) (hQwB : Qw ≤ B) (hE : 0 ≤ E) (hV : 0 ≤ V) :
    allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin ≤
      allocatedWitnessScaleLog B (2 * B + 2 * V + 5 * E + 24) := by
  have hPB : Pseed ≤ B := le_trans (le_add_of_nonneg_right hPmin) hB
  have hB0 : 0 ≤ B := hPseed.trans hPB
  have hscale : allocatedScaleLog Pseed + (1 + Pseed ^ 2) * Pmin ≤
      allocatedScaleLog B := by
    unfold allocatedScaleLog
    calc
      (1 + Pseed ^ 2) * (5 * Pseed + 49) + (1 + Pseed ^ 2) * Pmin =
          (1 + Pseed ^ 2) * (5 * Pseed + Pmin + 49) := by ring
      _ ≤ (1 + B ^ 2) * (5 * B + 49) := by
        apply mul_le_mul
        · gcongr
        · linarith
        · positivity
        · positivity
  have hgap : Pseed ^ 2 * Qw ≤ B ^ 2 * (2 * B + 2 * V + 5 * E + 24) := by
    gcongr
    linarith
  unfold allocatedWitnessScaleLog
  linarith

theorem preparedCertifiedSameScaleBadProductInterface_of_lateFloor
    {B0 Elog Vlog Pseed Qw Pmin : ℝ} (Q : ℕ)
    (hB : 1 ≤ B0) (hMB : (M : ℝ) ≤ B0) (hnXB : (nX : ℝ) ≤ B0)
    (hElogB : Elog ∈ Set.Icc 0 B0) (hVlogB : Vlog ∈ Set.Icc 0 B0)
    (hQ : 1 ≤ Q) (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp B0) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp B0)
    (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hseedFloor : Pseed + Pmin ≤ B0) (hQwB : Qw ≤ B0)
    (hS : (S.value : ℝ) ≤ Real.exp
      (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M)) Elog Vlog Q ≤
          (layerSamplerGapWidth (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j,i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    PreparedCertifiedSameScaleBadProductInterface prep U b S B0 Elog Vlog Q := by
  apply preparedCertifiedSameScaleBadProductInterface_of_bounds prep U b S Q
    hB hMB hnXB hElogB hVlogB hQ hQexp hmpos hCoord hRi hσi
  · exact hS.trans (Real.exp_le_exp.mpr (allocatedWitnessScaleLog_lateFloor_le
      hPseed hQw hPmin hseedFloor hQwB hElogB.1 hVlogB.1))
  · exact hprincipal

theorem preparedCertifiedSameScaleBadProductInterface_of_late_parameters
    {Pbase Elog Vlog Pseed Qw Pmin : ℝ} (Q : ℕ)
    (hbase : 0 ≤ Pbase) (hMB : (M : ℝ) ≤ Pbase) (hnXB : (nX : ℝ) ≤ Pbase)
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog)
    (hQ : 1 ≤ Q) (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pbase) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pbase)
    (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hS : (S.value : ℝ) ≤ Real.exp
      (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M)) Elog Vlog Q ≤
          (layerSamplerGapWidth (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j,i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    PreparedCertifiedSameScaleBadProductInterface prep U b S
      (1 + Pbase + Pseed + Qw + Pmin + Elog + Vlog) Elog Vlog Q := by
  let B0 := 1 + Pbase + Pseed + Qw + Pmin + Elog + Vlog
  have hbaseB : Pbase ≤ B0 := by dsimp [B0]; linarith
  have hB : 1 ≤ B0 := by dsimp [B0]; linarith
  have hElogB : Elog ∈ Set.Icc 0 B0 := ⟨hElog, by dsimp [B0]; linarith⟩
  have hVlogB : Vlog ∈ Set.Icc 0 B0 := ⟨hVlog, by dsimp [B0]; linarith⟩
  apply preparedCertifiedSameScaleBadProductInterface_of_lateFloor prep U b S Q
    hB (hMB.trans hbaseB) (hnXB.trans hbaseB) hElogB hVlogB hQ hQexp hmpos hCoord
  · exact fun j => (hRi j).trans (Real.exp_le_exp.mpr hbaseB)
  · exact fun j => (hσi j).trans (Real.exp_le_exp.mpr hbaseB)
  · exact hPseed
  · exact hQw
  · exact hPmin
  · dsimp [B0]; linarith
  · dsimp [B0]; linarith
  · exact hS
  · exact hprincipal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

private theorem lateTolerance_base_bounds {Bstruct Pscale pRadius : ℝ}
    (hBstruct : 0 ≤ Bstruct) (hPscale : 0 ≤ Pscale) (hpRadius : 0 ≤ pRadius) :
    0 ≤ Bstruct + Pscale + pRadius ∧
      Bstruct ≤ Bstruct + Pscale + pRadius ∧
      pRadius ≤ Bstruct + Pscale + pRadius ∧
      Pscale ≤ Bstruct + Pscale + pRadius := by
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

private theorem lateTolerance_larger_bounds
    {Bstruct pRadius Pscale Pseed Qw Pmin Elog Vlog Bcert : ℝ}
    (hBstruct : 0 ≤ Bstruct) (hpRadius : 0 ≤ pRadius) (hPscale : 0 ≤ Pscale)
    (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog)
    (hcert : 1 + (Bstruct + Pscale + pRadius) + Pseed + Qw + Pmin + Elog + Vlog ≤ Bcert) :
    1 ≤ Bcert ∧ Bstruct ≤ Bcert ∧ pRadius ≤ Bcert ∧ Pscale ≤ Bcert ∧
      Elog ≤ Bcert ∧ Vlog ≤ Bcert ∧ Pseed + Pmin ≤ Bcert ∧ Qw ≤ Bcert := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

theorem preparedCertifiedSameScaleBadProductInterface_of_lateTolerance
    {Bstruct pRadius Pscale Pseed Qw Pmin Elog Vlog : ℝ} (Q : ℕ)
    (hBstruct : 0 ≤ Bstruct) (hpRadius : 0 ≤ pRadius) (hPscale : 0 ≤ Pscale)
    (hM : (M : ℝ) ≤ Bstruct) (hnX : (nX : ℝ) ≤ Bstruct)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pscale)
    (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog)
    (hQ : 1 ≤ Q) (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hS : (S.value : ℝ) ≤ Real.exp
      (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M)) Elog Vlog Q ≤
          (layerSamplerGapWidth (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j,i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    PreparedCertifiedSameScaleBadProductInterface prep U b S
      (1 + (Bstruct + Pscale + pRadius) + Pseed + Qw + Pmin + Elog + Vlog) Elog Vlog Q := by
  obtain ⟨hbase, hstruct, hradius, hscale⟩ := lateTolerance_base_bounds hBstruct hPscale hpRadius
  exact preparedCertifiedSameScaleBadProductInterface_of_late_parameters
    (nX := nX) (M := M) prep U b S
    (Pbase := Bstruct + Pscale + pRadius) (Elog := Elog) (Vlog := Vlog)
    (Pseed := Pseed) (Qw := Qw) (Pmin := Pmin) Q
    hbase (hM.trans hstruct) (hnX.trans hstruct) hElog hVlog hQ hQexp hmpos hCoord
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hradius))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hscale))
    hPseed hQw hPmin hS hprincipal

theorem preparedCertifiedSameScaleBadProductInterface_of_lateTolerance_larger
    {Bstruct pRadius Pscale Pseed Qw Pmin Elog Vlog : ℝ} (Q : ℕ)
    (hBstruct : 0 ≤ Bstruct) (hpRadius : 0 ≤ pRadius) (hPscale : 0 ≤ Pscale)
    (hM : (M : ℝ) ≤ Bstruct) (hnX : (nX : ℝ) ≤ Bstruct)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pscale)
    (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog)
    (hQ : 1 ≤ Q) (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hS : (S.value : ℝ) ≤ Real.exp
      (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M)) Elog Vlog Q ≤
          (layerSamplerGapWidth (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j,i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    ∀ Bcert : ℝ,
      1 + (Bstruct + Pscale + pRadius) + Pseed + Qw + Pmin + Elog + Vlog ≤ Bcert →
      PreparedCertifiedSameScaleBadProductInterface prep U b S Bcert Elog Vlog Q := by
  intro Bcert hcert
  obtain ⟨hB, hstruct, hradius, hscale, hEB, hVB, hseedFloor, hQwB⟩ :=
    lateTolerance_larger_bounds hBstruct hpRadius hPscale hPseed hQw hPmin hElog hVlog hcert
  exact preparedCertifiedSameScaleBadProductInterface_of_lateFloor
    (nX := nX) (M := M) prep U b S
    (B0 := Bcert) (Elog := Elog) (Vlog := Vlog)
    (Pseed := Pseed) (Qw := Qw) (Pmin := Pmin) Q
    hB (hM.trans hstruct) (hnX.trans hstruct) ⟨hElog, hEB⟩ ⟨hVlog, hVB⟩
    hQ hQexp hmpos hCoord
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hradius))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hscale))
    hPseed hQw hPmin hseedFloor hQwB hS hprincipal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

theorem preparedShortCertifiedSameScaleBadProductInterface_of_lateFloor
    {B0 Elog Vlog Pseed Qw Pmin : ℝ} (Q : ℕ)
    (hB : 1 ≤ B0) (hMB : (M : ℝ) ≤ B0) (hnXB : (nX : ℝ) ≤ B0)
    (hElogB : Elog ∈ Set.Icc 0 B0) (hVlogB : Vlog ∈ Set.Icc 0 B0)
    (hQ : 1 ≤ Q) (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp B0) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp B0)
    (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hseedFloor : Pseed + Pmin ≤ B0) (hQwB : Qw ≤ B0)
    (hS : (S.value : ℝ) ≤ Real.exp
      (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M)) Elog Vlog Q ≤
          (layerSamplerGapWidth (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j,i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    PreparedShortCertifiedSameScaleBadProductInterface prep U b S B0 Elog Vlog Q := by
  apply preparedShortCertifiedSameScaleBadProductInterface_of_bounds prep U b S Q
    hB hMB hnXB hElogB hVlogB hQ hQexp hmpos hCoord hRi hσi
  · exact hS.trans (Real.exp_le_exp.mpr (allocatedWitnessScaleLog_lateFloor_le
      hPseed hQw hPmin hseedFloor hQwB hElogB.1 hVlogB.1))
  · exact hprincipal

theorem preparedShortCertifiedSameScaleBadProductInterface_of_late_parameters
    {Pbase Elog Vlog Pseed Qw Pmin : ℝ} (Q : ℕ)
    (hbase : 0 ≤ Pbase) (hMB : (M : ℝ) ≤ Pbase) (hnXB : (nX : ℝ) ≤ Pbase)
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog)
    (hQ : 1 ≤ Q) (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pbase) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pbase)
    (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hS : (S.value : ℝ) ≤ Real.exp
      (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M)) Elog Vlog Q ≤
          (layerSamplerGapWidth (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j,i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    PreparedShortCertifiedSameScaleBadProductInterface prep U b S
      (1 + Pbase + Pseed + Qw + Pmin + Elog + Vlog) Elog Vlog Q := by
  let B0 := 1 + Pbase + Pseed + Qw + Pmin + Elog + Vlog
  have hbaseB : Pbase ≤ B0 := by dsimp [B0]; linarith
  have hB : 1 ≤ B0 := by dsimp [B0]; linarith
  have hElogB : Elog ∈ Set.Icc 0 B0 := ⟨hElog, by dsimp [B0]; linarith⟩
  have hVlogB : Vlog ∈ Set.Icc 0 B0 := ⟨hVlog, by dsimp [B0]; linarith⟩
  apply preparedShortCertifiedSameScaleBadProductInterface_of_lateFloor prep U b S Q
    hB (hMB.trans hbaseB) (hnXB.trans hbaseB) hElogB hVlogB hQ hQexp hmpos hCoord
  · exact fun j => (hRi j).trans (Real.exp_le_exp.mpr hbaseB)
  · exact fun j => (hσi j).trans (Real.exp_le_exp.mpr hbaseB)
  · exact hPseed
  · exact hQw
  · exact hPmin
  · dsimp [B0]; linarith
  · dsimp [B0]; linarith
  · exact hS
  · exact hprincipal

end Erdos3.VectorPolynomial

end

end OAI

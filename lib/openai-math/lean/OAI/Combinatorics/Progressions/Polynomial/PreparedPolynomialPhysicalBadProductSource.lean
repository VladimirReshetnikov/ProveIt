import OAI.Combinatorics.Progressions.Dynamics.PreparedSameScaleBadProductBudget
import OAI.Combinatorics.Progressions.Estimates.PreparedPhysicalBadProductSource

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def preparedBadProductCoefficientExponent (m : ℕ) : ℕ :=
  (exists_preparedBadProductFinalBudget m).choose
noncomputable def preparedBadProductSpatialExponent (m : ℕ) : ℕ :=
  (exists_preparedBadProductFinalBudget m).choose_spec.choose

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S0 : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

variable (Elog Vlog : ℝ) (Q : ℕ)

include bW hC hV in

theorem exists_prepared_polynomial_physical_bad_product_source
    {B : ℝ} (hB : 1 ≤ B) (hMB : (M : ℝ) ≤ B) (hnXB : (nX : ℝ) ≤ B)
    (hElogB : Elog ∈ Set.Icc 0 B) (hVlogB : Vlog ∈ Set.Icc 0 B) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    {P0 : ℝ} (hP0B : P0 ∈ Set.Icc 0 B)
    (hsourceBudget : allocatedComparisonDimension m ((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) : ℝ) ≤ P0)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P0) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P0)
    (hS0 : (S0.value : ℝ) ≤ Real.exp P0) :
    let P := (B + preparedBadProductCoefficientExponent m) ^ preparedBadProductCoefficientExponent m
    let Ps := (B + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m
    ∃ S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := ((fun j : Fin m => RankPreparationLayer.Coord (prep j)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ,
      S0.value ≤ S.value ∧
      (S.value : ℝ) ≤ Real.exp P ∧
      ∀
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
 := by
  intro P Ps
  have hbudget := (exists_preparedBadProductFinalBudget m).choose_spec.choose_spec
  obtain ⟨hP1, hPs1, hBP, hP0P, hprimitive, hPscale, hbudgetP, hframe, hPPS, hWlog, hfreq, hmass⟩ :=
    hbudget.2.2 hB hMB hnXB hP0B hElogB hVlogB
  have hP : 0 ≤ P := zero_le_one.trans hP1
  have hPs : 0 ≤ Ps := zero_le_one.trans hPs1
  have hbudgetPs := hbudgetP.trans hPPS
  obtain ⟨S, hle, hS, htail⟩ := exists_prepared_physical_bad_product_source prep U bW b hb o S0 C V hC hV
    Elog Vlog Q hElogB.1 hVlogB.1 hQ hQexp hmpos hCoord hR hσ hσ1 hsourceBudget hRi hσi hS0
  refine ⟨S, hle, hS.trans (Real.exp_le_exp.mpr hPscale), ?_⟩
  intro Cinv hCinv hchart hsmall hAP hCP hVP
    instLattice instCompact instMeasurable instBorel μ instLeft instProbability ν instνLeft instνProb
    poly hp hm ρ Rs Smax hρ hρPs stride hstride
    hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells width hwidth hwide
  have hcounts : (((m + 1) * (enlargedPreparedCommonSamplerDimension m M
        (modularInitialBlockCount m (nX + m * M)) + 1) ^ m +
        enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M)) : ℕ) : ℝ) ≤ P := by
    simpa only [P, preparedBadProductCoefficientExponent, Nat.cast_add] using hprimitive
  exact htail Cinv hCinv hchart hsmall hP hcounts
    (hAP.trans (Real.exp_le_exp.mpr hBP))
    (fun j => (hCP j).trans (Real.exp_le_exp.mpr hBP))
    (fun j => (hVP j).trans (Real.exp_le_exp.mpr hBP)) hbudgetP μ ν poly hp hm
    hPs hframe hbudgetPs hρ (hρPs.trans (Real.exp_le_exp.mpr (hBP.trans hPPS))) stride hstride
    hSmax (hSmaxPs.trans (Real.exp_le_exp.mpr (hBP.trans hPPS))) hstrideMax
    H hsize hrank hRs cells hcells width hwidth hwide hfreq hmass hP0P hPscale hPPS hWlog

end Erdos3.VectorPolynomial

end

end OAI

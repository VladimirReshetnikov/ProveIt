import OAI.Combinatorics.Progressions.Dynamics.PreparedJointPhysicalScalarBudget
import OAI.Combinatorics.Progressions.Dynamics.PreparedSourceSideBudget
import OAI.Combinatorics.Progressions.Estimates.PreparedCenteredModelMarginalData
import OAI.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorProductive
import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialDenseSliceCenter
import OAI.Combinatorics.Progressions.Linear.PreparedRoundedRank
import OAI.Combinatorics.Progressions.Polynomial.PreparedCenteredJointGoodPolynomial
import OAI.Combinatorics.Progressions.Sampling.AllocatedRetainedActualForecastFactory

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_preparedCentered_forecastGoodData (m : ℕ) :
    ∃ A Asp : ℕ, 4 ≤ A ∧ 2 ≤ Asp ∧
    (∀ {P₀ gainLog : ℝ} {n : ℕ}, 0 ≤ P₀ → 0 < n → (n : ℝ) ≤ P₀ →
      0 ≤ gainLog → gainLog ≤ P₀ →
      (spatialMatrixBlockThreshold n (jointSpatialError gainLog))⁻¹ ≤
        Real.exp ((P₀ + Asp) ^ Asp)) ∧
    ∀ {nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (B0 Vlog gainLog gain : ℝ) (Q : ℕ)
    (_hsource : PreparedCertifiedSameScaleBadProductInterface prep U b S B0 (gainLog + 8) Vlog Q)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
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
    {Pchart Pmaster Plate D Pwidth P₀ P : ℝ}
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp Pchart)
    (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp Pchart)
    (_hchartB : Pchart ≤ B0)
    (_hMaster : 0 ≤ Pmaster) (_hLate : Pmaster ≤ Plate)
    (_hd : AllocatedComparisonDimensions (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (Fin (0 + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1) : Type)) D)
    (_hD : D ≤ Pmaster) (_hnMaster : (nX : ℝ) ≤ Pmaster)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (_hS : (S.value : ℝ) ≤ Real.exp Plate)
    (_hprojection : (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate).Pproj ≤ Pwidth)
    (_hphysical : jointPhysicalBaseLog Pwidth (gainLog + 8) Vlog ≤ B0)
    (_hVlog : 0 ≤ Vlog) (_hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (_hP₀ : 0 ≤ P₀) (_hnP₀ : (nX : ℝ) ≤ P₀) (_hgP₀ : gainLog ≤ P₀)
    (_hcutoffP : (P₀ + Asp) ^ Asp ≤ P)
    (_hBP : B0 ≤ P) (_hwidthP : Pwidth ≤ P)
    (_hg : 0 ≤ gainLog) (_hgP : gainLog + 8 ≤ P) (_hgain : Real.exp (-gainLog) ≤ gain)
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
    (stride : Fin nX → ℕ) (_hstride : ∀ x, 0 < stride x)
    (_hstrideP : ∀ x, (stride x : ℝ) ≤ Real.exp Pwidth)
    {τ ξ : ℝ} (hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp Pwidth)
    (hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp Pwidth),
    let W := allocatedPhysicalRootBudget (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ => 0)
    let required := max
      ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) +
        allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m)
      ((P + A) ^ A)
    ∀ (N : Fin nX → ℕ) (hN : ∀ x, 0 < N x),
    (∀ x, Real.exp required ≤ (N x : ℝ)) →
    ∀ {Rs : ℝ},
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun x => (N x : ℝ)) Rs (U j) (poly j)) →
    Real.exp required ≤ Rs →
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride)),
    cells.Nonempty →
    let width := narrowTrimmedSpatialWidths (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) W τ ξ N
    let hwidth := narrowTrimmedSpatialWidths_pos
      (allocatedPhysicalRootBudget_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ => 0)) hτ hξ N hN
    ∀ (bases : Finset (Fin nX → ℤ)) (hbases : bases.Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
      {Eforecast : ℝ}
      (hnormalizerCenter : ∀ center,
        let Z := selectedJointDensityMass bases stride cells width
          (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center)
        |Z - 1| ≤ Real.exp (-Eforecast) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
          0 < Z ∧ Z⁻¹ ≤ 2)
      (_hnX : 0 < nX)
      (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))),
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      let law := fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hmass (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (allocatedCenteredJointDensity_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (hnormalizerCenter center).2.2.1
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U ×
          (bases × rectangularWeightIndices 0 width 1)),
          MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ law).real bad ≤ (gain / 4) / 4 ∧
          ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, z ∉ bad →
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c z.1) z.2.1.val z.2.2.val (sample z.1 z.2.1.val z.2.2.val) (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.2.val (t,j,i))| := by
  obtain ⟨A, Asp, hA, hAsp, hκ, hgood⟩ := exists_preparedCentered_jointGoodPolynomial m
  refine ⟨A, Asp, hA, hAsp, hκ, ?_⟩
  intro nX M X₀ J₀ prep U b R σ S B0 Vlog gainLog gain Q hsource E _ bW hb o C V hC hV
    hR hσ hσ1 Cinv hCinv hchart hsmall Pchart Pmaster Plate D Pwidth P₀ P
    hprofile hCP hVP hchartB hMaster hLate hd hD hnMaster hRi hσi hS hprojection
    hphysical hVlog hQexp hP₀ hnP₀ hgP₀ hcutoffP hBP hwidthP hg hgP hgain
    _ _ _ _ μ _ _ ν _ _ poly hp hm stride hstride hstrideP τ ξ hτ hτP hξ hξ1 hξP
    W required N hN hsize Rs hrank hRs cells hcells width hwidth bases hbases hmass
    Eforecast hnormalizerCenter hnX e
  have hproj := preparedCenteredMarginalProjectionBounds (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S o
    (s := 0) hMaster hLate hd hD hnMaster hRi hσi hS
  have hPwidth : 0 ≤ Pwidth := hproj.Pproj_nonneg.trans hprojection
  have hP : 0 ≤ P := hPwidth.trans hwidthP
  have hprojP := hprojection.trans hwidthP
  have hExpProjection := Real.exp_le_exp.mpr hprojP
  have hExpWidth := Real.exp_le_exp.mpr hwidthP
  have hExpChart := Real.exp_le_exp.mpr hchartB
  have hExpPhysical := Real.exp_le_exp.mpr hphysical
  have hW : 0 ≤ W := allocatedPhysicalRootBudget_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ => 0)
  have hWP : W ≤ Real.exp Pwidth := hproj.root_projection.trans
    (Real.exp_le_exp.mpr hprojection)
  obtain ⟨_, _, _, _, hρ, hρinv, hSmax, hSmaxB, hstrideMax, hwide⟩ :=
    jointPhysicalScalarBudget (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)))
      hPwidth hW hWP hτ hτP hξ hξ1 hξP (by linarith : 0 ≤ gainLog + 8)
      hVlog Q hQexp stride hstrideP
  have hsizeMod (x) := (Real.exp_le_exp.mpr (le_max_left _ _)).trans (hsize x)
  have hsizeSpatial (x) := (Real.exp_le_exp.mpr (le_max_right _ _)).trans (hsize x)
  have hRsMod := (Real.exp_le_exp.mpr (le_max_left _ _)).trans hRs
  have hRsSpatial := (Real.exp_le_exp.mpr (le_max_right _ _)).trans hRs
  exact hgood prep U b S B0 Vlog gainLog gain Q hsource bW hb o C V hC hV
    hR hσ hσ1 Cinv hCinv hchart hsmall (hprofile.trans hExpChart)
    (fun j => (hCP j).trans hExpChart) (fun j => (hVP j).trans hExpChart)
    μ ν poly hp hm hρ (hρinv.trans hExpPhysical) stride hstride
    hSmax (hSmaxB.trans hExpPhysical) hstrideMax N hsizeMod hrank hRsMod
    cells hcells width hwidth (hwide N hN) bases hbases hmass
    (fun center => (hnormalizerCenter center).2.2.1)
    hP₀ hnP₀ hgP₀ hcutoffP hP hBP hg hgP hgain
    (hproj.m_projection.trans hprojP) (hproj.variables_projection.trans hprojP)
    (by simpa only [Fintype.card_fin] using hproj.X_projection.trans hprojP)
    (hproj.frame_projection.trans hprojP)
    (fun j => (hproj.Rinv_projection j).trans hExpProjection)
    (fun j => (hproj.σinv_projection j).trans hExpProjection)
    (fun j => (hproj.coefficient_projection j).trans hprojP)
    (fun j => (hproj.I_projection j).trans hprojP)
    (fun j => (hproj.n_projection j).trans hprojP)
    (fun j => (hproj.J_projection j).trans hprojP)
    (hproj.S_projection.trans hExpProjection)
    (fun x => (hstrideP x).trans hExpWidth) hW (hWP.trans hExpWidth)
    hτ (hτP.trans hExpWidth) hξ hξ1 (hξP.trans hExpWidth)
    hsizeSpatial hRsSpatial rfl hnX e

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredForecastGoodConclusion
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) : Prop :=
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U ×
          (bases × rectangularWeightIndices 0 width 1)),
          MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ law).real bad ≤ (gain / 4) / 4 ∧
          ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, z ∉ bad →
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c z.1) z.2.1.val z.2.2.val (sample z.1 z.2.1.val z.2.2.val) (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedGridAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.2.val (t,j,i))|

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable def preparedCenteredForecastGoodExponent (m : ℕ) : ℕ :=
  (exists_preparedCentered_forecastGoodData m).choose

noncomputable def preparedCenteredForecastSpatialExponent (m : ℕ) : ℕ :=
  (exists_preparedCentered_forecastGoodData m).choose_spec.choose

theorem preparedCenteredForecastGoodExponent_ge (m : ℕ) :
    4 ≤ preparedCenteredForecastGoodExponent m :=
  (exists_preparedCentered_forecastGoodData m).choose_spec.choose_spec.1

theorem preparedCenteredForecastSpatialExponent_ge (m : ℕ) :
    2 ≤ preparedCenteredForecastSpatialExponent m :=
  (exists_preparedCentered_forecastGoodData m).choose_spec.choose_spec.2.1

theorem preparedCenteredForecast_spatialThreshold_inv (m : ℕ)
    {P₀ gainLog : ℝ} {n : ℕ} (hP₀ : 0 ≤ P₀) (hn : 0 < n) (hnP₀ : (n : ℝ) ≤ P₀)
    (hg : 0 ≤ gainLog) (hgP₀ : gainLog ≤ P₀) :
    (spatialMatrixBlockThreshold n (jointSpatialError gainLog))⁻¹ ≤
      Real.exp ((P₀ + preparedCenteredForecastSpatialExponent m) ^
        preparedCenteredForecastSpatialExponent m) :=
  (exists_preparedCentered_forecastGoodData m).choose_spec.choose_spec.2.2.1
    hP₀ hn hnP₀ hg hgP₀

noncomputable def preparedCenteredForecastGoodRequired (m : ℕ) (B0 Pgood : ℝ) : ℝ :=
  max ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) +
    allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m)
    ((Pgood + preparedCenteredForecastGoodExponent m) ^ preparedCenteredForecastGoodExponent m)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredForecastGoodProperty
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (stride : Fin nX → ℕ)
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) : Prop :=
  PreparedCenteredForecastGoodConclusion prep U b S bW hb o hR hσ μ poly hm
    stride width bases gainLog gain Q e law

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredShortForecastGoodConclusion
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) : Prop :=
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U ×
          (bases × rectangularWeightIndices 0 width 1)),
          MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ law).real bad ≤ (gain / 4) / 4 ∧
          ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, z ∉ bad →
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c z.1) z.2.1.val z.2.2.val (sample z.1 z.2.1.val z.2.2.val) (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.2.val (t,j,i))|

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredForecastReadFamily
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (c : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → ∀ j, U j)
    (sample : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → CoefficientSamplerArrays (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
    (read : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ)
    : Prop :=
  (∀ center a, AllocatedCenteredRecoveredSampleReadAt (L := modularInitialBlockCount m (nX + m * M)) (m := m) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (X := Fin nX) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (E := E) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm
        (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ)
        center (c center) a (sample center a) (read center a))

def PreparedCenteredForecastPathPoint
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)]
    [BorelSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (physicalN : Fin nX → ℕ) (τ ξ gainLog Pdim Qstride : ℝ)
    (bases : Finset (Fin nX → ℤ)) (e : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    (c : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → ∀ j, U j)
    (sample : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → CoefficientSamplerArrays (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
    (read : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ)
    (primes : Finset ℕ) (depth : ℕ → ℕ)
    (commonTuple : (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) → IntegerScalarCubeBox Empty S.value)
    (prescribed : ℕ → ℕ)
    (origin : ∀ p : primes, LayerSamplerLongVariables (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value) (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ZMod (p.val ^ depth p.val))
    (δslice Ppres : ℝ)
    (lower swidth : ∀ a : {a : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) // ¬(allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value) a},
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) a.val × Fin (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) a.val) → ℝ)
    (z : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) × (bases × rectangularWeightIndices (0 : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) ((narrowTrimmedSpatialWidths (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) (allocatedPhysicalRootBudget (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ : (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) => 0)) τ ξ physicalN) : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) 1)) : Prop :=
          ∃ path : ActualFixedSpatialForecastPath (Lrank := modularInitialBlockCount m (nX + m * M)) (Tsp := SpatialKernelRemainder e) (m := m) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (X := Fin nX) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (Eout := E) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S hR hσ
            (nX + m * M) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) (spatialTwoBlockEquiv (X := Fin nX) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) e) (allocatedPhysicalRootBudget (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ : (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) => 0)) S.value physicalN
            τ δslice (Pdim * (Pdim + 1) + (((Pdim + preparedCenteredForecastThresholdExponent) ^ preparedCenteredForecastThresholdExponent) + 2) + Pdim ^ 2 + Pdim) (2 * (Fintype.card (Fin nX) : ℝ) * Qstride + (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11) Ppres,
            path.center = c z.1 ∧ path.base = z.2.1.val ∧ path.noise = z.2.2.val ∧
            path.sample = sample z.1 z.2.1.val z.2.2.val ∧
            path.read = allocatedReplaceReadNoise (m := m) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (X := Fin nX) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (E := E) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) z.2.2.val
              (allocatedJointFrameRead (m := m) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (X := Fin nX) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (E := E) (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) z.2.1.val (read z.1 z.2.1.val z.2.2.val)) ∧
            path.commonTuple = commonTuple ∧ path.primes = primes ∧ path.exponent = depth ∧
            path.prescribed = prescribed ∧ HEq path.origin origin ∧ path.lower = lower ∧ path.width = swidth ∧
            AllocatedCenteredFramedRecoveredSampleAt (m := m) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (X := Fin nX) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (E := E) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              path.center path.base path.noise path.sample
              (allocatedJointFrameRead (m := m) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (X := Fin nX) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (E := E) (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) z.2.1.val (read z.1 z.2.1.val z.2.2.val))

def PreparedCenteredForecastPathContinuation
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)]
    [BorelSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (physicalN : Fin nX → ℕ) (τ ξ gainLog Pdim Qstride : ℝ)
    (bases : Finset (Fin nX → ℤ)) (e : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    (μ : Measure (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)) (gain : ℝ) (Q : ℕ)
    (law : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices (0 : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) ((narrowTrimmedSpatialWidths (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) (allocatedPhysicalRootBudget (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ : (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) => 0)) τ ξ physicalN) : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) 1))
    (c : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → ∀ j, U j)
    (sample : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → CoefficientSamplerArrays (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
    (read : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ)
    : Prop :=
      ∀ (primes : Finset ℕ) (_hprime : ∀ p ∈ primes, p.Prime)
        (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
      ∃ bad : Set ((CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) × (bases × rectangularWeightIndices (0 : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) ((narrowTrimmedSpatialWidths (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) (allocatedPhysicalRootBudget (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ : (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) => 0)) τ ξ physicalN) : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) 1)),
        MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ law).real bad ≤ (gain / 4) / 4 ∧
        ∀ (commonTuple : (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) → IntegerScalarCubeBox Empty S.value)
          (prescribed : ℕ → ℕ)
          (origin : ∀ p : primes, LayerSamplerLongVariables (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value) (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ZMod (p.val ^ depth p.val))
          (δslice Ppres : ℝ)
          (_hpres : ((∏ p : primes, p.val ^ prescribed p.val : ℕ) : ℝ) ≤ Real.exp Ppres)
          (lower swidth : ∀ a : {a : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) // ¬(allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value) a},
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) a.val × Fin (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) a.val) → ℝ),
          (∀ a p, δslice ≤ swidth a p) → (∀ a p, 0 ≤ lower a p) →
          (∀ a p, |lower a p| + |swidth a p| ≤ 1) →
        ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, z ∉ bad →
          PreparedCenteredForecastPathPoint (prep := prep) (nX := nX) (M := M) (U := U) (b := b) (S := S) (E := E) (hb := hb) (o := o) (hR := hR) (hσ := hσ) (poly := poly) (hm := hm) (c := c) (sample := sample) (read := read) (physicalN := physicalN) (τ := τ) (ξ := ξ) (bases := bases) (e := e) (Pdim := Pdim) (Qstride := Qstride) (gainLog := gainLog) primes depth commonTuple prescribed origin δslice Ppres lower swidth z

theorem exists_preparedCentered_forecastPathFamily
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)]
    [BorelSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (physicalN : Fin nX → ℕ) (τ ξ gainLog Pdim Qstride : ℝ)
    (bases : Finset (Fin nX → ℤ)) (e : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    (μ : Measure (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)) (gain : ℝ) (Q : ℕ)
    (law : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices (0 : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) ((narrowTrimmedSpatialWidths (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) (allocatedPhysicalRootBudget (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ : (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) => 0)) τ ξ physicalN) : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) 1))
    (hgood : PreparedCenteredShortForecastGoodConclusion (m := m) (nX := nX) (M := M) prep U b S bW hb o hR hσ μ poly hm
      stride (narrowTrimmedSpatialWidths (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) (allocatedPhysicalRootBudget (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ : (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) => 0)) τ ξ physicalN) bases gainLog gain Q e law)
    (hPdim : 0 ≤ Pdim) (hnX : 0 < nX) (hX : (nX : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤ Pdim)
    (hgainLog : 0 ≤ gainLog) (hgainDim : gainLog ≤ Pdim)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ x, 0 < physicalN x) :
    ∃ c : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → ∀ j, U j, Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → CoefficientSamplerArrays (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
        AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      PreparedCenteredForecastReadFamily (prep := prep) (nX := nX) (M := M) (U := U) (b := b) (S := S) (E := E) (hb := hb) (o := o) (hR := hR) (hσ := hσ) (poly := poly) (hm := hm) (c := c) (sample := sample) (read := read) (bW := bW) ∧
      PreparedCenteredForecastPathContinuation (prep := prep) (nX := nX) (M := M) (U := U) (b := b) (S := S) (E := E) (hb := hb) (o := o) (hR := hR) (hσ := hσ) (poly := poly) (hm := hm) (c := c) (sample := sample) (read := read) (physicalN := physicalN) (τ := τ) (ξ := ξ) (bases := bases) (e := e) (Pdim := Pdim) (Qstride := Qstride) (gainLog := gainLog) (μ := μ) (law := law) (gain := gain) (Q := Q) := by
  obtain ⟨c,hc,hcenter,sample,read,hread,hgood⟩ := hgood
  refine ⟨c,hc,hcenter,sample,read,hread,?_⟩
  intro primes hprime depth hdepth
  let : ∀ p : primes, NeZero p.val := actualForecastPrimeNeZero primes hprime
  obtain ⟨bad,hbad,hbadMass,hgood⟩ := hgood primes hprime depth hdepth
  refine ⟨bad,hbad,hbadMass,?_⟩
  intro commonTuple prescribed origin δslice Ppres hpres lower swidth hwidth hlower hcontained
  filter_upwards [hgood] with z hz
  intro hzbad
  obtain ⟨hrecovered,hproduct,hdet⟩ := hz hzbad
  have hproduct' := hproduct
  rw [modularInitialRankStrength_eq_forecast] at hproduct'
  have hκinv := preparedCenteredForecast_threshold_inverse hPdim hnX hX hgainLog hgainDim
  let path := preparedCenteredGoodActualForecastPath (m := m) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (X := Fin nX) (Eout := E) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S hR hσ hb o poly hm
    (nX + m * M) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) e physicalN τ ξ δslice Pdim ((Pdim + preparedCenteredForecastThresholdExponent) ^ preparedCenteredForecastThresholdExponent) Ppres gainLog Qstride
    z.2.1.val z.2.2.val (c z.1) (sample z.1 z.2.1.val z.2.2.val)
    (allocatedJointFrameRead (m := m) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (X := Fin nX) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (E := E) (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) z.2.1.val (read z.1 z.2.1.val z.2.2.val)) hrecovered
    commonTuple primes hprime depth prescribed origin stride hproduct' hpres
    lower swidth hwidth hlower hcontained hPdim (by simpa using hX) hvars hτ hξ hN
    z.2.2.property (by simpa using hnX) hgainLog hstride (by simpa using hκinv)
    (by simpa using hdet)
  refine ⟨path, rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl,rfl,rfl,?_⟩
  exact hrecovered

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredShortForecastGoodProperty
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (stride : Fin nX → ℕ)
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) : Prop :=
  PreparedCenteredShortForecastGoodConclusion prep U b S bW hb o hR hσ μ poly hm
    stride width bases gainLog gain Q e law

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredSlicedForecastPathPoint
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)]
    [BorelSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (physicalN : Fin nX → ℕ) (τ ξ : ℝ)
    (bases : Finset (Fin nX → ℤ)) (e : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    (c : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → ∀ j, U j)
    (sample : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → CoefficientSamplerArrays (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
    (read : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ)
    (primes : Finset ℕ) (depth : ℕ → ℕ)
    {A : Type} [Fintype A] (selected : A → Σ j : Fin m, Fin ((preparedSamplerTransverse prep) j))
    (δslice : ℝ)
    (s : ActualFixedSpatialForecastSetup (X := Fin nX) (Eout := E)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (nX + m * M) selected τ δslice)
    (q : ActualFixedSpatialSlicedForecastNumerics s)
    (z : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) × (bases × rectangularWeightIndices (0 : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) ((narrowTrimmedSpatialWidths (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) (allocatedPhysicalRootBudget (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ : (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) => 0)) τ ξ physicalN) : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) 1)) : Prop :=

          ∃ path : ActualFixedSpatialForecastPath (Lrank := modularInitialBlockCount m (nX + m * M)) (Tsp := SpatialKernelRemainder e) (m := m) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (X := Fin nX) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (Eout := E) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S hR hσ
            (nX + m * M) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) (spatialTwoBlockEquiv (X := Fin nX) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) e) (allocatedPhysicalRootBudget (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ : (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) => 0)) S.value physicalN
            τ 1 s.P s.Pbad 0,
          ∀ input : ActualFixedSpatialDenseSliceInput s q,
            let member := path.toDenseSliceMember input
            member.slice.path.center = c z.1 ∧ member.slice.path.base = z.2.1.val ∧ member.slice.path.noise = z.2.2.val ∧
            member.slice.path.sample = sample z.1 z.2.1.val z.2.2.val ∧
            member.slice.path.read = allocatedReplaceReadNoise (m := m) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (X := Fin nX) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (E := E) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) z.2.2.val
              (allocatedJointFrameRead (m := m) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (X := Fin nX) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (E := E) (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) z.2.1.val (read z.1 z.2.1.val z.2.2.val)) ∧
            member.slice.path.primes = primes ∧ member.slice.path.exponent = depth ∧
            AllocatedCenteredFramedRecoveredSampleAt (m := m) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (X := Fin nX) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (E := E) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              member.slice.path.center member.slice.path.base member.slice.path.noise member.slice.path.sample
              (allocatedJointFrameRead (m := m) (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (X := Fin nX) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (E := E) (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) z.2.1.val (read z.1 z.2.1.val z.2.2.val))

def PreparedCenteredSlicedForecastPathContinuation
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)]
    [BorelSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (physicalN : Fin nX → ℕ) (τ ξ : ℝ)
    (bases : Finset (Fin nX → ℤ)) (e : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    (μ : Measure (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)) (gain : ℝ) (Q : ℕ)
    (law : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices (0 : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) ((narrowTrimmedSpatialWidths (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) (allocatedPhysicalRootBudget (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ : (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) => 0)) τ ξ physicalN) : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) 1))
    (c : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → ∀ j, U j)
    (sample : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → CoefficientSamplerArrays (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
    (read : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ)

    {A : Type} [Fintype A] (selected : A → Σ j : Fin m, Fin ((preparedSamplerTransverse prep) j))
    (δslice : ℝ)
    (s : ActualFixedSpatialForecastSetup (X := Fin nX) (Eout := E)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (nX + m * M) selected τ δslice)
    (q : ActualFixedSpatialSlicedForecastNumerics s) : Prop :=
      ∀ (primes : Finset ℕ) (_hprime : ∀ p ∈ primes, p.Prime)
        (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
      ∃ bad : Set ((CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) × (bases × rectangularWeightIndices (0 : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) ((narrowTrimmedSpatialWidths (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) (allocatedPhysicalRootBudget (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ : (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) => 0)) τ ξ physicalN) : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) 1)),
        MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ law).real bad ≤ (gain / 4) / 4 ∧
        ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, z ∉ bad →
          PreparedCenteredSlicedForecastPathPoint (prep := prep) (nX := nX) (M := M) (U := U) (b := b) (S := S) (E := E) (hb := hb) (o := o) (hR := hR) (hσ := hσ) (poly := poly) (hm := hm) (c := c) (sample := sample) (read := read) (physicalN := physicalN) (τ := τ) (ξ := ξ) (bases := bases) (e := e) primes depth selected δslice s q z

theorem exists_preparedCentered_slicedForecastPathFamily
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)]
    [BorelSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (physicalN : Fin nX → ℕ) (τ ξ gainLog Pdim Qstride : ℝ)
    (bases : Finset (Fin nX → ℤ)) (e : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    (μ : Measure (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U)) (gain : ℝ) (Q : ℕ)
    (law : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices (0 : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) ((narrowTrimmedSpatialWidths (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) (allocatedPhysicalRootBudget (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ : (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) => 0)) τ ξ physicalN) : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) 1))
    (hgood : PreparedCenteredShortForecastGoodConclusion (m := m) (nX := nX) (M := M) prep U b S bW hb o hR hσ μ poly hm
      stride (narrowTrimmedSpatialWidths (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) (allocatedPhysicalRootBudget (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ : (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) => 0)) τ ξ physicalN) bases gainLog gain Q e law)
    (hPdim : 0 ≤ Pdim) (hnX : 0 < nX) (hX : (nX : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤ Pdim)
    (hgainLog : 0 ≤ gainLog) (hgainDim : gainLog ≤ Pdim)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ x, 0 < physicalN x)
    {A : Type} [Fintype A] (selected : A → Σ j : Fin m, Fin ((preparedSamplerTransverse prep) j))
    (δslice : ℝ)
    (s : ActualFixedSpatialForecastSetup (X := Fin nX) (Eout := E)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (nX + m * M) selected τ δslice)
    (q : ActualFixedSpatialSlicedForecastNumerics s)
    (hPmodel : preparedCenteredForecastSpatialLog Pdim ≤ s.P)
    (hPbad : 2 * (Fintype.card (Fin nX) : ℝ) * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11 ≤ s.Pbad) :
    ∃ c : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → ∀ j, U j, Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → CoefficientSamplerArrays (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) U) → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
        AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      PreparedCenteredForecastReadFamily (prep := prep) (nX := nX) (M := M) (U := U) (b := b) (S := S) (E := E) (hb := hb) (o := o) (hR := hR) (hσ := hσ) (poly := poly) (hm := hm) (c := c) (sample := sample) (read := read) (bW := bW) ∧
      PreparedCenteredSlicedForecastPathContinuation (prep := prep) (nX := nX) (M := M) (U := U) (b := b) (S := S) (E := E) (hb := hb) (o := o) (hR := hR) (hσ := hσ) (poly := poly) (hm := hm) (c := c) (sample := sample) (read := read) (physicalN := physicalN) (τ := τ) (ξ := ξ) (bases := bases) (e := e) (μ := μ) (law := law) (gain := gain) (Q := Q) selected δslice s q := by
  obtain ⟨c, hc, hcenter, sample, read, hread, hpaths⟩ :=
    exists_preparedCentered_forecastPathFamily prep U b S bW hb o hR hσ poly hm
      stride physicalN τ ξ gainLog Pdim Qstride bases e μ gain Q law hgood
      hPdim hnX hX hvars hgainLog hgainDim hstride hτ hξ hN
  refine ⟨c, hc, hcenter, sample, read, hread, ?_⟩
  intro primes hprime depth hdepth
  obtain ⟨bad, hbad, hmass, hpaths⟩ := hpaths primes hprime depth hdepth
  refine ⟨bad, hbad, hmass, ?_⟩
  let xzero : (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) → IntegerScalarCubeBox Empty S.value :=
    fun _ _ => ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast S.positive⟩⟩
  have hpres : ((∏ p : primes, p.val ^ (0 : ℕ) : ℕ) : ℝ) ≤ Real.exp 0 := by simp
  have hp := hpaths xzero (fun _ => 0) (fun _ _ => 0) 1 0 hpres
    (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ _ => by norm_num)
  filter_upwards [hp] with z hz
  intro hzbad
  obtain ⟨path, hcpath, hbpath, hnpath, hsample, hrpath, _, hprimes, hdepth', _, _, _, _, hrecovered⟩ := hz hzbad
  let adjusted : ActualFixedSpatialForecastPath (Eout := E)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S hR hσ
      (nX + m * M) (preparedInitialRankSpatialEmbedding (m := m) nX M)
      (preparedInitialRankKernelEmbedding (m := m) nX M)
      (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value))
      (spatialTwoBlockEquiv e)
      (allocatedPhysicalRootBudget (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ => 0))
      S.value physicalN τ 1 s.P s.Pbad 0 :=
    { path with
      hjac := path.hjac.trans (Real.exp_le_exp.mpr hPmodel)
      hinverse := path.hinverse.trans (Real.exp_le_exp.mpr hPmodel)
      RbadBound := path.RbadBound.trans (Real.exp_le_exp.mpr hPbad) }
  refine ⟨adjusted, ?_⟩
  intro input
  exact ⟨hcpath, hbpath, hnpath, hsample, hrpath, hprimes, hdepth', hrecovered⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m nX M : ℕ} {J₀ : Type}
variable (prep : RankPreparationFamily (Fin nX) J₀ m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
    {U : ∀ j, Submodule ℝ ((prep j).Coord → ℝ)}
    {b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : (Fin nX) → ℕ} {poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((prep j).Coord → ℝ)}
    {hm : ∀ j ex, coefficients (poly j) ex ∈ U j}
    {τ ξ : ℝ} {stride : (Fin nX) → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U}
    {A : AllocatedExternalCandidateSampler (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S hb o hR hσ N poly hm τ ξ stride cells center}

theorem exists_preparedRetainedActualForecastFactory
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace (U j))))
    (centerLift : ∀ j, U j)
    (sampleFn : ((Fin nX) → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × (Fin nX) → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
    (readFn : ((Fin nX) → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × (Fin nX) → ℤ) →
      AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ)
    (productive retained : Finset A.Path) (hsub : retained ⊆ productive)
    (e : Fin 2 × (Fin nX) ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (Pdim gainLog Qstride Ptest : ℝ)
    (hglobal : ∀ base, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ
      poly hm (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ)
      center centerLift base (sampleFn base) (readFn base))
    (hrecovered : ∀ z ∈ productive, AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ
      poly hm centerLift z.1.val z.2.val (sampleFn z.1.val z.2.val)
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val)))
    (hgood : let primes := boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊
      letI := actualForecastPrimeNeZero primes (boundedPrimes_prime _)
      ∀ z ∈ productive,
      (∏ p ∈ primes, p ^ largestTestedBadDepth (fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
        (allocatedActualPrimeBad (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value)
          (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val))) ≤
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius (gainLog + 8)))
    (hdet : ∀ z ∈ productive, ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card (Fin nX)) (jointSpatialError gainLog) / 2 <
        |Matrix.det (fun i j : (Fin nX) => spatialMatrixNormalizedEntries e A.widths z.2.val (t,j,i))|)
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card (Fin nX) : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤ Pdim)
    (hnX : 0 < Fintype.card (Fin nX)) (hgainLog : 0 ≤ gainLog) (hgainDim : gainLog ≤ Pdim)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    {Selected : Type} {selected : Selected → Σ j : Fin m, Fin ((preparedSamplerTransverse prep) j)} {δslice : ℝ}
    (setup : ActualFixedSpatialForecastSetup (X := (Fin nX)) (Eout := E)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (nX + m * M) selected τ δslice)
    (hPmodel : preparedCenteredForecastSpatialLog Pdim ≤ setup.P)
    (hPbad : 2 * Fintype.card (Fin nX) * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11 ≤ setup.Pbad) :
    AllocatedRetainedActualForecastFactoryConclusion bW centerLift sampleFn readFn retained
      (nX + m * M) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) e Ptest (modularInitialRankStrength m (nX + m * M) : ℝ) setup := by
  have hgood' := hgood
  rw [modularInitialRankStrength_eq_forecast] at hgood'
  have hdet' := hdet
  have hdecX : instDecidableEqFin nX =
      (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  rw [hdecX] at hdet'
  exact exists_allocatedRetainedActualForecastFactory (A := A)
    bW centerLift sampleFn readFn productive retained hsub (nX + m * M) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value))
    e Pdim gainLog Qstride Ptest (modularInitialRankStrength m (nX + m * M) : ℝ) hglobal hrecovered hgood' hdet'
    hPdim hX hvars hnX hgainLog hgainDim hstride setup hPmodel hPbad

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedForecastProductiveRequired (m : ℕ)
    (Pmaster Plate E B0 Pgood Pprod : ℝ) : ℝ :=
  let r := preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m 0) 1 Pmaster Plate
  max (max r.required ((max r.Pproj E + preparedCenteredMarginalExponent m) ^
    preparedCenteredMarginalExponent m))
    (max (preparedCenteredForecastGoodRequired m B0 Pgood)
      ((Pprod + preparedModularGeneralProductivityExponent m) ^
        preparedModularGeneralProductivityExponent m))

theorem exists_preparedForecastRequired_power_budget (m inputPower : ℕ) :
    ∃ outputPower : ℕ, 2 ≤ outputPower ∧ ∀ p : ℝ, 2 ≤ p →
      ∀ Pmaster Plate E B0 Pgood Pprod : ℝ,
        0 ≤ Pmaster → Pmaster ≤ Plate → Plate ≤ (p + 2) ^ inputPower →
        E ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        B0 ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Pgood ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Pprod ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        preparedForecastProductiveRequired m Pmaster Plate E B0 Pgood Pprod ≤
          (p + 2) ^ outputPower := by
  obtain ⟨C, _, hresources⟩ := exists_preparedModularGeneralDetector_resource_budget
    (preparedModularGeneralDetectorConstants m 0) 1
  let Am := preparedCenteredMarginalExponent m
  let Ab := preparedBadProductSpatialExponent m
  let At := allocatedMaskedTiltedConstant m
  let Ag := preparedCenteredForecastGoodExponent m
  let Ap := preparedModularGeneralProductivityExponent m
  let U : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower
  let B : Polynomial ℕ := (2 * U + Polynomial.C C) ^ C
  let Q : Polynomial ℕ := B + (B + U + Polynomial.C Am) ^ Am +
    ((U + Polynomial.C Ab) ^ Ab + Polynomial.C At) ^ At +
    (U + Polynomial.C Ag) ^ Ag + (U + Polynomial.C Ap) ^ Ap
  obtain ⟨outputPower, houtputPower, hQ⟩ := exists_natPolynomial_fixed_power_budget Q
  refine ⟨outputPower, houtputPower, ?_⟩
  intro p hp Pmaster Plate E B0 Pgood Pprod hMaster hLate hPlate hE hB0 hGood hProd
  let u := (p + 2) ^ inputPower
  let b := (2 * u + C) ^ C
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hmaster : Pmaster ≤ u := hLate.trans hPlate
  have hres := (hresources hMaster hLate).1
  have hresbound : (Pmaster + Plate + C) ^ C ≤ b :=
    pow_le_pow_left₀ (by have := hMaster.trans hLate; positivity)
      (by change Pmaster + Plate + C ≤ 2 * u + C; linarith) C
  have hrequired := hres.required.2.trans hresbound
  have hproj := hres.Pproj.2.trans hresbound
  let r := preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m 0) 1 Pmaster Plate
  have hmarg : (max r.Pproj E + Am) ^ Am ≤ (b + u + Am) ^ Am := by
    apply pow_le_pow_left₀
      (add_nonneg (hres.Pproj.1.trans (le_max_left _ _)) (Nat.cast_nonneg Am))
    exact add_le_add (max_le (by change r.Pproj ≤ b + u; linarith)
      (by change E ≤ b + u; have := hE.2; linarith)) le_rfl
  have hbad : ((B0 + Ab) ^ Ab + At) ^ At ≤ ((u + Ab) ^ Ab + At) ^ At := by
    apply pow_le_pow_left₀ (by have := hB0.1; positivity)
    exact add_le_add (pow_le_pow_left₀ (by have := hB0.1; positivity)
      (add_le_add hB0.2 le_rfl) Ab) le_rfl
  have hgood : (Pgood + Ag) ^ Ag ≤ (u + Ag) ^ Ag :=
    pow_le_pow_left₀ (by have := hGood.1; positivity) (add_le_add hGood.2 le_rfl) Ag
  have hprod : (Pprod + Ap) ^ Ap ≤ (u + Ap) ^ Ap :=
    pow_le_pow_left₀ (by have := hProd.1; positivity) (add_le_add hProd.2 le_rfl) Ap
  have hmarg0 : 0 ≤ (b + u + Am) ^ Am := by positivity
  have hbad0 : 0 ≤ ((u + Ab) ^ Ab + At) ^ At := by positivity
  have hgood0 : 0 ≤ (u + Ag) ^ Ag := by positivity
  have hprod0 : 0 ≤ (u + Ap) ^ Ap := by positivity
  have htotal : b + (b + u + Am) ^ Am + ((u + Ab) ^ Ab + At) ^ At +
      (u + Ag) ^ Ag + (u + Ap) ^ Ap ≤ (p + 2) ^ outputPower := by
    simpa [Q, B, U, b, u, Polynomial.eval₂_pow] using hQ p (by linarith : 0 ≤ p)
  change max (max r.required ((max r.Pproj E + Am) ^ Am))
    (max (max (((B0 + Ab) ^ Ab + At) ^ At) ((Pgood + Ag) ^ Ag))
      ((Pprod + Ap) ^ Ap)) ≤ _
  apply max_le
  · apply max_le
    · change r.required ≤ _
      linarith
    · linarith
  · apply max_le
    · exact max_le (by linarith) (by linarith)
    · linarith

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Polynomial.PreparedCenteredShortJointGoodPolynomial
import OAI.Combinatorics.Progressions.Sampling.PreparedCenteredForecastModelExtensionAnd

namespace OAI

section

namespace Erdos3

def preparedForecastGoodCertificateBudget (baseB₀ Pchart Pwidth g V : ℝ) : ℝ :=
  1 + baseB₀ + Pchart + jointPhysicalBaseLog Pwidth (g + 8) V

def preparedForecastGoodAnalyticBudget (Asp : ℕ) (baseB₀ Pchart Pwidth g V : ℝ) : ℝ :=
  preparedForecastGoodCertificateBudget baseB₀ Pchart Pwidth g V + Pwidth +
    (Pchart + Asp) ^ Asp + g + 9

theorem preparedForecastGoodBudgets (Asp : ℕ) {baseB₀ Pchart Pwidth g V : ℝ}
    (hbase : 0 ≤ baseB₀) (hchart : 0 ≤ Pchart) (hwidth : 0 ≤ Pwidth)
    (hg : 0 ≤ g) (hV : 0 ≤ V) :
    let Bcert := preparedForecastGoodCertificateBudget baseB₀ Pchart Pwidth g V
    let Pgood := preparedForecastGoodAnalyticBudget Asp baseB₀ Pchart Pwidth g V
    0 ≤ Bcert ∧ baseB₀ ≤ Bcert ∧ Pchart ≤ Bcert ∧
      jointPhysicalBaseLog Pwidth (g + 8) V ≤ Bcert ∧
      0 ≤ Pgood ∧ Bcert ≤ Pgood ∧ Pwidth ≤ Pgood ∧
      (Pchart + Asp) ^ Asp ≤ Pgood ∧ g + 8 ≤ Pgood := by
  intro Bcert Pgood
  have hphysical : 0 ≤ jointPhysicalBaseLog Pwidth (g + 8) V := by
    unfold jointPhysicalBaseLog
    positivity
  have hcert : 0 ≤ Bcert := by
    dsimp only [Bcert, preparedForecastGoodCertificateBudget]
    positivity
  have hpower : 0 ≤ (Pchart + Asp) ^ Asp := by positivity
  have hgood : 0 ≤ Pgood := by
    change 0 ≤ Bcert + Pwidth + (Pchart + Asp) ^ Asp + g + 9
    positivity
  have hdef : Bcert = 1 + baseB₀ + Pchart + jointPhysicalBaseLog Pwidth (g + 8) V := rfl
  have hgdef : Pgood = Bcert + Pwidth + (Pchart + Asp) ^ Asp + g + 9 := rfl
  refine ⟨hcert, ?_, ?_, ?_, hgood, ?_, ?_, ?_, ?_⟩ <;>
    linarith only [hdef, hgdef, hbase, hchart, hwidth, hg, hphysical, hcert, hpower]

theorem exists_preparedForecastGoodBudgets_bound (Asp : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P baseB₀ Pchart Pwidth g V : ℝ},
      0 ≤ P → baseB₀ ∈ Set.Icc 0 P → Pchart ∈ Set.Icc 0 P →
      Pwidth ∈ Set.Icc 0 P → g ∈ Set.Icc 0 P → V ∈ Set.Icc 0 P →
      preparedForecastGoodCertificateBudget baseB₀ Pchart Pwidth g V ∈
        Set.Icc 0 ((P + C) ^ C) ∧
      preparedForecastGoodAnalyticBudget Asp baseB₀ Pchart Pwidth g V ∈
        Set.Icc 0 ((P + C) ^ C) := by
  let poly : Polynomial ℕ :=
    15 * Polynomial.X + 160 + (Polynomial.X + Polynomial.C Asp) ^ Asp
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro P baseB₀ Pchart Pwidth g V hP hbase hchart hwidth hg hV
  obtain ⟨hcert, _, _, _, hgood, hcertGood, _, _, _⟩ :=
    preparedForecastGoodBudgets Asp hbase.1 hchart.1 hwidth.1 hg.1 hV.1
  have hpow : (Pchart + Asp) ^ Asp ≤ (P + Asp) ^ Asp :=
    pow_le_pow_left₀ (add_nonneg hchart.1 (Nat.cast_nonneg _))
      (add_le_add hchart.2 (le_refl (Asp : ℝ))) Asp
  have hgoodUpper : preparedForecastGoodAnalyticBudget Asp baseB₀ Pchart Pwidth g V ≤
      15 * P + 160 + (P + Asp) ^ Asp := by
    unfold preparedForecastGoodAnalyticBudget preparedForecastGoodCertificateBudget jointPhysicalBaseLog
    linarith only [hbase.2, hchart.2, hwidth.2, hg.2, hV.2, hpow]
  have hpoly : 15 * P + 160 + (P + Asp) ^ Asp ≤ (P + C) ^ C := by
    simpa [poly, Polynomial.eval₂_pow] using hbound P hP
  exact ⟨⟨hcert, hcertGood.trans (hgoodUpper.trans hpoly)⟩,
    ⟨hgood, hgoodUpper.trans hpoly⟩⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_preparedCentered_short_forecastGoodData (m : ℕ) :
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
    (_hsource : PreparedShortCertifiedSameScaleBadProductInterface prep U b S B0 (gainLog + 8) Vlog Q)
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
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
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
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.2.val (t,j,i))| := by
  obtain ⟨A, Asp, hA, hAsp, hκ, hgood⟩ := exists_preparedCentered_short_jointGoodPolynomial m
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
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable def preparedCenteredShortForecastGoodExponent (m : ℕ) : ℕ :=
  (exists_preparedCentered_short_forecastGoodData m).choose

noncomputable def preparedCenteredShortForecastSpatialExponent (m : ℕ) : ℕ :=
  (exists_preparedCentered_short_forecastGoodData m).choose_spec.choose

theorem preparedCenteredShortForecastGoodExponent_ge (m : ℕ) :
    4 ≤ preparedCenteredShortForecastGoodExponent m :=
  (exists_preparedCentered_short_forecastGoodData m).choose_spec.choose_spec.1

theorem preparedCenteredShortForecastSpatialExponent_ge (m : ℕ) :
    2 ≤ preparedCenteredShortForecastSpatialExponent m :=
  (exists_preparedCentered_short_forecastGoodData m).choose_spec.choose_spec.2.1

theorem preparedCenteredShortForecast_spatialThreshold_inv (m : ℕ)
    {P₀ gainLog : ℝ} {n : ℕ} (hP₀ : 0 ≤ P₀) (hn : 0 < n) (hnP₀ : (n : ℝ) ≤ P₀)
    (hg : 0 ≤ gainLog) (hgP₀ : gainLog ≤ P₀) :
    (spatialMatrixBlockThreshold n (jointSpatialError gainLog))⁻¹ ≤
      Real.exp ((P₀ + preparedCenteredShortForecastSpatialExponent m) ^
        preparedCenteredShortForecastSpatialExponent m) :=
  (exists_preparedCentered_short_forecastGoodData m).choose_spec.choose_spec.2.2.1
    hP₀ hn hnP₀ hg hgP₀

noncomputable def preparedCenteredShortForecastGoodRequired (m : ℕ) (B0 Pgood : ℝ) : ℝ :=
  max ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) +
    allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m)
    ((Pgood + preparedCenteredShortForecastGoodExponent m) ^ preparedCenteredShortForecastGoodExponent m)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedShortForecastProductiveRequired (m : ℕ)
    (Pmaster Plate E B0 Pgood Pprod : ℝ) : ℝ :=
  let r := preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m 0) 1 Pmaster Plate
  max (max r.required ((max r.Pproj E + preparedCenteredMarginalExponent m) ^
    preparedCenteredMarginalExponent m))
    (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
      ((Pprod + preparedModularGeneralProductivityExponent m) ^
        preparedModularGeneralProductivityExponent m))

theorem exists_preparedShortForecastRequired_power_budget (m inputPower : ℕ) :
    ∃ outputPower : ℕ, 2 ≤ outputPower ∧ ∀ p : ℝ, 2 ≤ p →
      ∀ Pmaster Plate E B0 Pgood Pprod : ℝ,
        0 ≤ Pmaster → Pmaster ≤ Plate → Plate ≤ (p + 2) ^ inputPower →
        E ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        B0 ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Pgood ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Pprod ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        preparedShortForecastProductiveRequired m Pmaster Plate E B0 Pgood Pprod ≤
          (p + 2) ^ outputPower := by
  obtain ⟨C, _, hresources⟩ := exists_preparedModularGeneralDetector_resource_budget
    (preparedModularGeneralDetectorConstants m 0) 1
  let Am := preparedCenteredMarginalExponent m
  let Ab := preparedBadProductSpatialExponent m
  let At := allocatedMaskedTiltedConstant m
  let Ag := preparedCenteredShortForecastGoodExponent m
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

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedForecastConstructedRequired_power_budget (m inputPower : ℕ) :
    ∃ outputPower : ℕ, 2 ≤ outputPower ∧ ∀ p : ℝ, 2 ≤ p →
      ∀ Pmaster Plate Eforecast baseB0 Pchart gainLog Vlog : ℝ,
        0 ≤ Pmaster → Pmaster ≤ Plate → Plate ≤ (p + 2) ^ inputPower →
        Eforecast ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        baseB0 ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Pchart ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        gainLog ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Vlog ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        let Pwidth := 4 * (Plate + 8)^2
        preparedForecastProductiveRequired m Pmaster Plate Eforecast
          (preparedForecastGoodCertificateBudget baseB0 Pchart Pwidth gainLog Vlog)
          (preparedForecastGoodAnalyticBudget (preparedCenteredForecastSpatialExponent m)
            baseB0 Pchart Pwidth gainLog Vlog) Pwidth ≤ (p + 2)^outputPower := by
  obtain ⟨C, _, hGoodBudgets⟩ :=
    exists_preparedForecastGoodBudgets_bound (preparedCenteredForecastSpatialExponent m)
  let U : Polynomial ℕ := (Polynomial.X + 2)^inputPower
  let W : Polynomial ℕ := U + 4 * (U + 8)^2
  let Q : Polynomial ℕ := W + (W + Polynomial.C C)^C
  obtain ⟨inflatedPower, _, hInflated⟩ := exists_natPolynomial_fixed_power_budget Q
  obtain ⟨outputPower, houtputPower, hRequired⟩ :=
    exists_preparedForecastRequired_power_budget m inflatedPower
  refine ⟨outputPower, houtputPower, ?_⟩
  intro p hp Pmaster Plate Eforecast baseB0 Pchart gainLog Vlog
    hMaster hLate hPlate hE hBase hChart hGain hV
  let u := (p + 2)^inputPower
  let w := u + 4 * (u + 8)^2
  let Pwidth := 4 * (Plate + 8)^2
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have huw : u ≤ w := by dsimp only [w]; nlinarith [sq_nonneg (u + 8)]
  have hw : 0 ≤ w := hu.trans huw
  have hwidth0 : 0 ≤ Pwidth := by dsimp only [Pwidth]; positivity
  have hLate0 : 0 ≤ Plate := hMaster.trans hLate
  have hwidth : Pwidth ≤ w := by
    have hsquare : (Plate + 8)^2 ≤ (u + 8)^2 :=
      pow_le_pow_left₀ (by linarith) (add_le_add hPlate le_rfl) 2
    dsimp only [Pwidth, w]
    nlinarith
  have hBcertGood := hGoodBudgets hw
    ⟨hBase.1, hBase.2.trans huw⟩ ⟨hChart.1, hChart.2.trans huw⟩
    ⟨hwidth0, hwidth⟩ ⟨hGain.1, hGain.2.trans huw⟩ ⟨hV.1, hV.2.trans huw⟩
  have hpower0 : 0 ≤ (w + C)^C := by positivity
  have hInflatedReal : w + (w + C)^C ≤ (p + 2)^inflatedPower := by
    simpa [Q, W, U, w, u, Polynomial.eval₂_pow] using hInflated p (by linarith : 0 ≤ p)
  have hwInflated : w ≤ (p + 2)^inflatedPower :=
    (le_add_of_nonneg_right hpower0).trans hInflatedReal
  have hpowerInflated : (w + C)^C ≤ (p + 2)^inflatedPower :=
    (le_add_of_nonneg_left hw).trans hInflatedReal
  exact hRequired p hp Pmaster Plate Eforecast
    (preparedForecastGoodCertificateBudget baseB0 Pchart Pwidth gainLog Vlog)
    (preparedForecastGoodAnalyticBudget (preparedCenteredForecastSpatialExponent m)
      baseB0 Pchart Pwidth gainLog Vlog) Pwidth hMaster hLate
    (hPlate.trans (huw.trans hwInflated))
    ⟨hE.1, hE.2.trans (huw.trans hwInflated)⟩
    ⟨hBcertGood.1.1, hBcertGood.1.2.trans hpowerInflated⟩
    ⟨hBcertGood.2.1, hBcertGood.2.2.trans hpowerInflated⟩
    ⟨hwidth0, hwidth.trans hwInflated⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedShortForecastConstructedRequired_power_budget (m inputPower : ℕ) :
    ∃ outputPower : ℕ, 2 ≤ outputPower ∧ ∀ p : ℝ, 2 ≤ p →
      ∀ Pmaster Plate Eforecast baseB0 Pchart gainLog Vlog : ℝ,
        0 ≤ Pmaster → Pmaster ≤ Plate → Plate ≤ (p + 2) ^ inputPower →
        Eforecast ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        baseB0 ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Pchart ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        gainLog ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Vlog ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        let Pwidth := 4 * (Plate + 8)^2
        preparedShortForecastProductiveRequired m Pmaster Plate Eforecast
          (preparedForecastGoodCertificateBudget baseB0 Pchart Pwidth gainLog Vlog)
          (preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent m)
            baseB0 Pchart Pwidth gainLog Vlog) Pwidth ≤ (p + 2)^outputPower := by
  obtain ⟨C, _, hGoodBudgets⟩ :=
    exists_preparedForecastGoodBudgets_bound (preparedCenteredShortForecastSpatialExponent m)
  let U : Polynomial ℕ := (Polynomial.X + 2)^inputPower
  let W : Polynomial ℕ := U + 4 * (U + 8)^2
  let Q : Polynomial ℕ := W + (W + Polynomial.C C)^C
  obtain ⟨inflatedPower, _, hInflated⟩ := exists_natPolynomial_fixed_power_budget Q
  obtain ⟨outputPower, houtputPower, hRequired⟩ :=
    exists_preparedShortForecastRequired_power_budget m inflatedPower
  refine ⟨outputPower, houtputPower, ?_⟩
  intro p hp Pmaster Plate Eforecast baseB0 Pchart gainLog Vlog
    hMaster hLate hPlate hE hBase hChart hGain hV
  let u := (p + 2)^inputPower
  let w := u + 4 * (u + 8)^2
  let Pwidth := 4 * (Plate + 8)^2
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have huw : u ≤ w := by dsimp only [w]; nlinarith [sq_nonneg (u + 8)]
  have hw : 0 ≤ w := hu.trans huw
  have hwidth0 : 0 ≤ Pwidth := by dsimp only [Pwidth]; positivity
  have hLate0 : 0 ≤ Plate := hMaster.trans hLate
  have hwidth : Pwidth ≤ w := by
    have hsquare : (Plate + 8)^2 ≤ (u + 8)^2 :=
      pow_le_pow_left₀ (by linarith) (add_le_add hPlate le_rfl) 2
    dsimp only [Pwidth, w]
    nlinarith
  have hBcertGood := hGoodBudgets hw
    ⟨hBase.1, hBase.2.trans huw⟩ ⟨hChart.1, hChart.2.trans huw⟩
    ⟨hwidth0, hwidth⟩ ⟨hGain.1, hGain.2.trans huw⟩ ⟨hV.1, hV.2.trans huw⟩
  have hpower0 : 0 ≤ (w + C)^C := by positivity
  have hInflatedReal : w + (w + C)^C ≤ (p + 2)^inflatedPower := by
    simpa [Q, W, U, w, u, Polynomial.eval₂_pow] using hInflated p (by linarith : 0 ≤ p)
  have hwInflated : w ≤ (p + 2)^inflatedPower :=
    (le_add_of_nonneg_right hpower0).trans hInflatedReal
  have hpowerInflated : (w + C)^C ≤ (p + 2)^inflatedPower :=
    (le_add_of_nonneg_left hw).trans hInflatedReal
  exact hRequired p hp Pmaster Plate Eforecast
    (preparedForecastGoodCertificateBudget baseB0 Pchart Pwidth gainLog Vlog)
    (preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent m)
      baseB0 Pchart Pwidth gainLog Vlog) Pwidth hMaster hLate
    (hPlate.trans (huw.trans hwInflated))
    ⟨hE.1, hE.2.trans (huw.trans hwInflated)⟩
    ⟨hBcertGood.1.1, hBcertGood.1.2.trans hpowerInflated⟩
    ⟨hBcertGood.2.1, hBcertGood.2.2.trans hpowerInflated⟩
    ⟨hwidth0, hwidth.trans hwInflated⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}
variable (prep : RankPreparationFamily X₀ J₀ m)
local notation "kernel" => EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))
local notation "blocks" => EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))
local notation "axes" => PreparedSamplerContinuous prep
local notation "transverse" => preparedSamplerTransverse prep
local notation "coords" => (fun j : Fin m => RankPreparationLayer.Coord (prep j))
variable (U : ∀ j, Submodule ℝ (coords j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (transverse j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := kernel) (I := axes) (n := transverse) (J := coords) blocks U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (0 + 1))))
variable (selection : Fin (0 + 1) ↪ kernel) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog uSource pModel
local notation "qDetect" => allocatedModelTestLog uSource pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (axes j)) (transverse j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables kernel axes transverse blocks))
variable (τ u p forecastCap : ℝ)
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := axes) U b S.value
local notation "degree" => layerSamplerDegree axes transverse
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => blocks (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => blocks (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides blocks U b S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos blocks U b S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (axes j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j))))

local notation "source" => allocatedCoefficientSource blocks U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource blocks U b hR hσ S
local notation "reference" => allocatedLongJetReference blocks U b S jetRows
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (0 + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity blocks U b hb o hR hσ S

def PreparedCenteredShortForecastGoodModelInterface
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (B0 gainLog gain Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) : Prop := by
  exact PreparedCenteredForecastModelExtensionInterface
    (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (μ := μ)
    (Good := PreparedCenteredShortForecastGoodProperty (m := m) (nX := nX) (M := M) prep U b S bW hb o hR hσ μ
      stride gainLog gain Qgood spatialEmbedding)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    (preparedCenteredShortForecastGoodRequired m B0 Pgood)

end Erdos3.VectorPolynomial

end

end OAI

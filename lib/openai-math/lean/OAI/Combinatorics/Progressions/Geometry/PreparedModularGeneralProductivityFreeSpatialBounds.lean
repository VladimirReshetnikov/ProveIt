import OAI.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorProductive

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem preparedModularGeneral_productivity_early_spatial_bounds
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {Pmaster Plate Pprod D : ℝ} (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hProd : 4 * (Plate + 8) ^ 2 ≤ Pprod)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D)
    (hD : D ≤ Pmaster) {nX : ℕ} (hnXpos : 0 < nX) (hnX : (nX : ℝ) ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (hLLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp Pmaster)
    (hVP : ∀ j, (V j : ℝ) ≤ Real.exp Pmaster)
    (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : Fin nX → ℕ) (hs : ∀ d, 0 < stride d)
    (hsP : ∀ d, (stride d : ℝ) ≤ Real.exp Pmaster)
    {gainLog ξ : ℝ} (hg : 0 ≤ gainLog)
    (hGainMaster : gainLog + (nX : ℝ) + 8 ≤ Pmaster)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (N : Fin nX → ℕ) {rank : ℝ}
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (hCells : cells.Nonempty) :
    (∀ d, Real.exp ((Pprod + preparedModularGeneralProductivityExponent m) ^
      preparedModularGeneralProductivityExponent m) ≤ (N d : ℝ)) →
    Real.exp ((Pprod + preparedModularGeneralProductivityExponent m) ^
      preparedModularGeneralProductivityExponent m) ≤ rank →
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    ∃ (hN : ∀ i, 0 < N i) (hwidths : ∀ z, 0 < widths z)
      (hmargin : ∀ i, 2 * spatialTrimMargin τ N i < N i)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
      (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells widths (density center)),
    let law := fun center => selectedJointFiniteLaw bases
      (trimmedIntegerBox_nonempty N _ hmargin) stride cells widths hwidths hmass
      (density center) (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
      (hD center)
    (∀ center,
      let Z := selectedJointDensityMass bases stride cells widths (density center)
      |Z - 1| ≤ Real.exp (-Pprod) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ Z⁻¹ ≤ 2) ∧
    (∀ (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
      (c : ∀ j, U j),
      coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun a => c a.1))) →
      ∃ htotal : 0 < selectedJointDensityMass bases stride cells widths
          (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX)
            (fun j => subtractConstant (c j).val (p j))
            (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j))),
        allocatedOriginalPathLaw B U basis hb o hR hσ S (Fin nX)
          (fun j => subtractConstant (c j).val (p j))
          (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j))
          N hN (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
          (Real.exp_pos _) hξ stride cells hmass bases
          (trimmedIntegerBox_nonempty N _ hmargin) htotal = law center) ∧
    ∀ (test : (Fin nX → ℝ) → ℝ), (∀ x, |test x| ≤ 1) →
    ∀ gain : ℝ, Real.exp (-gainLog) ≤ gain →
      gain ≤ (𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) →
    let productive := Finset.univ.filter (fun z : bases × rectangularWeightIndices 0 widths 1 =>
      Function.Injective (fun q : Sites => jointIntegerPhysicalSite q.val (z.1.val,z.2.val)) ∧
        gain / 2 ≤ 𝔼 q : Sites, test
          (fun i => (jointIntegerPhysicalSite q.val (z.1.val,z.2.val) i : ℝ)))
    let joint := centeredFiniteProbabilityMeasure μ law
    IsProbabilityMeasure joint ∧
      MeasurableSet {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 widths 1) | z.2 ∈ productive} ∧
      gain / 4 ≤ joint.real {z | z.2 ∈ productive} ∧
      (∀ᵐ z ∂joint, ∃ c : ∀ j, U j,
        coefficientConstantCenter U z.1 =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun s => c s.1))) ∧
        allocatedAffineDensity B U basis hb o hR hσ S p hm c
          (fun k v => (jointIntegerFrame (z.2.1.val,z.2.2.val) k v : ℝ)) ≠ 0) ∧
      ∀ z : bases × rectangularWeightIndices 0 widths 1, ∀ q : Sites,
        jointIntegerPhysicalSite q.val (z.1.val,z.2.val) ∈ integerBox N := by
  intro hSize hRank τ W widths bases density sides Sites
  obtain ⟨hPτ, hτ, hτhalf, hτdim, hτeq, hτcap, hprecision⟩ :=
    preparedEarlySpatialWidth nX hg
  have hτP : τ⁻¹ ≤ Real.exp Pmaster := hτcap Pmaster hGainMaster
  have hPlate : 0 ≤ Plate := hMaster.trans hLate
  have hGainProd : gainLog + 8 ≤ Pprod := by
    have hnX0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
    nlinarith only [hGainMaster, hLate, hProd, hPlate, hnX0, sq_nonneg Plate]
  obtain ⟨hN, hwidths, hmargin, hmass, hDens, hnormal, htests⟩ :=
    preparedModularGeneral_productivity_bounds B U basis S hb o μ ν hR hσ hσ1
      C V hC hV Cinv hCinv hchart hsmall hMaster hLate hProd hd hD hnXpos hnX
      hRP hσLate hLLate hCP hVP p hp hm stride hs hsP
      hτ hτP hτhalf hξ hξ1 hξLate N hrank cells hCells hSize hRank
  refine ⟨hN, hwidths, hmargin, hmass, hDens, ?_⟩
  intro law
  refine ⟨hnormal, ?_, ?_⟩
  · intro center c hc
    exact preparedModularGeneralCenteredLaw B U basis hb o hR hσ S p hm N hN
      (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hτ hξ
      stride cells hmass bases (trimmedIntegerBox_nonempty N _ hmargin)
      center c hc (hDens center)
  · intro test htest gain hgain hscore
    obtain ⟨hcollision, herr⟩ := hprecision Pprod gain hGainProd hgain
    exact htests test htest gain ((Real.exp_pos _).trans_le hgain) hcollision herr hscore

end Erdos3.VectorPolynomial

end

end OAI

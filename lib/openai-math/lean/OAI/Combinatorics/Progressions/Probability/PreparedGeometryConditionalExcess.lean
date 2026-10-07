import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateFixedCenterExcess
import OAI.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeDirectMasterBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m nX s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U basis R σ}
    {hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : Fin nX → ℕ} {poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : Fin nX → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride)}

namespace AllocatedExternalCandidateSamplerFamily

noncomputable local instance preparedConditionalExcessFinDecidableEq : DecidableEq (Fin nX) := Classical.decEq _

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem prepared_conditional_excess
    (A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hm τ ξ stride cells)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {Cdetect : ℕ}
    {Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice E : ℝ}
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog sourceU pModel)
      pRadius (2 * sourceU + 4 * pModel + 7) pGain)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (Cforward Vtail : Fin m → ℝ≥0)
    (hforward : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ Cforward j * ‖z‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ C j * ‖z‖)
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hstrideBound : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hτInv : τ⁻¹ ≤ Real.exp Pphysical) (hτHalf : τ ≤ 1 / 2)
    (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    (hξone : ξ ≤ 1) (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (hsize : ∀ x, Real.exp ((max (4 * (Plate + 8) ^ 2) E +
      allocatedExternalConditionalExcessExponent m) ^ allocatedExternalConditionalExcessExponent m) ≤ (N x : ℝ))
    {rank : ℝ}
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun x => (N x : ℝ)) rank (U j) (poly j))
    (hRank : Real.exp ((max (4 * (Plate + 8) ^ 2) E +
      allocatedExternalConditionalExcessExponent m) ^ allocatedExternalConditionalExcessExponent m) ≤ rank)
    (hCells : cells.Nonempty) (hbox : (integerBox N).Nonempty)
    (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x) :
    ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
      letI : Nonempty (A center).Site := (A center).site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        ((A center).law.siteLaw ((A center).physicalBox hξone hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j)) ≤
          6 * positiveProjectionAccuracy E := by
  classical
  obtain ⟨⟨geometry⟩, _⟩ := geometryAt
  have hRi (j) : (R j)⁻¹ ≤ Real.exp pRadius := by
    have h := geometry.hK j
    simpa only [Real.coe_toNNReal (Real.exp pRadius) (Real.exp_pos pRadius).le] using h
  have hbnd := preparedCenteredMarginalProjectionBounds B U basis S o
    scalar.master_nonneg scalar.late geometry.hdimensions scalar.dimension_master
    scalar.ambient_master
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr scalar.radius_master))
    (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr scalar.scale_late)) hSLate
  have hChart := scalar.chart_master.trans hbnd.master_projection
  have hStride := scalar.stride_master.2.trans hbnd.master_projection
  have hPhysical := scalar.physical_master.2.trans hbnd.master_projection
  intro center
  exact (A center).fixedCenter_excess μ ν
    (fun j => (geometry.hσsmall j).trans geometry.htone)
    Cforward Vtail hforward hVactual C hC hchart
    (geometry.hbudgets C hC hCbound).1
    hbnd.Pproj_nonneg hbnd.m_projection hbnd.variables_projection hbnd.X_projection
    hbnd.frame_projection hbnd.Rinv_projection hbnd.σinv_projection
    hbnd.coefficient_projection hbnd.I_projection hbnd.n_projection hbnd.J_projection
    hbnd.profile_projection hbnd.S_projection
    (fun j => (hForward j).trans (Real.exp_le_exp.mpr hChart))
    (fun j => (hVtail j).trans (Real.exp_le_exp.mpr hChart)) hp
    (fun x => (hstrideBound x).trans (Real.exp_le_exp.mpr hStride))
    (by simpa only [allocatedExternalCandidateRootBudget_eq] using hbnd.root_projection)
    (hτInv.trans (Real.exp_le_exp.mpr hPhysical)) hτHalf
    (by simpa only [Fintype.card_fin] using hτDim) hξone
    (hξLate.trans (Real.exp_le_exp.mpr hbnd.late_projection)) hsize hrank hRank
    hCells hbox hmargin

end AllocatedExternalCandidateSamplerFamily
end Erdos3.VectorPolynomial

end

end OAI

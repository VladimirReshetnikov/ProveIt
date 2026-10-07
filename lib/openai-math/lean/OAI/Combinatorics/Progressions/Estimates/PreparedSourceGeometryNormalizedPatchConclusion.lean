import OAI.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateReturnedModulusBudget
import OAI.Combinatorics.Progressions.Dynamics.AllocatedNormalizationPrimitiveBudget
import OAI.Combinatorics.Progressions.Linear.RelativeActualRankBudget
import OAI.Combinatorics.Progressions.Polynomial.AllocatedZeroLayerDegreeScalarConclusion
import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateActualShearForecastScore
import OAI.Combinatorics.Progressions.Sampling.PreparedShearForecastScoreBridge
import OAI.Combinatorics.Progressions.Sampling.PreparedSourceSlicedForecastNumerics

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m : ℕ} {G X J₀ : Type} [Fintype G] [Fintype X]
variable (prep : RankPreparationFamily X J₀ m)
variable {preparationP : ℝ} {Rprep : ℕ}
variable (hprep : prep.PreparedHeights preparationP Rprep)
variable (hpPrep : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
variable {I Eout : Fin m → Type} [∀ j, Fintype (I j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod (allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) τ (Real.exp (-cost) / 2))
variable (qnum qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j))
  (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))]
variable (ν : ∀ j, Measure (euclideanSubspace ((fun j : Fin m => (prep j).space) j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (EuclideanJetLayers (fun j : Fin m => (prep j).space) (fun _ : Fin m => Unit))]
variable {stride : X → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) (fun j : Fin m => (prep j).space)}
variable {A : AllocatedExternalCandidateSampler B (fun j : Fin m => (prep j).space) b S hb o hR hσ N (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
  τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem.Conclusion
local instance : Nonempty A.Site := A.site_nonempty
variable {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {degree d t : ℕ}
variable (patch : PolynomialPatch Y degree d) [Fintype (PolynomialShearIndex patch.weight)]
variable {Fmark : NilpotentLieFiltration M t}
variable {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
variable {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) (fun j : Fin m => (prep j).Coord))}
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost massThreshold scoreThreshold outputMass outputScore : ℝ}
variable {P : AllocatedExternalCandidateProblem (E := Eout) A
  (polynomialShearNilmanifold patch.weight degree patch.weight_le) Fmark φ marked
  (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
  chartCost massThreshold scoreThreshold}
variable (out : P.Conclusion cost outputMass outputScore)
variable {δbase PpresBase : ℝ}
variable (path : ∀ _z : out.retained, ActualFixedSpatialForecastPath (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S hR hσ Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B (fun j : Fin m => (prep j).space) b S (fun _ => 0)) (S.value : ℝ) N τ δbase s.P s.Pbad PpresBase)
variable (hkeep : ∀ z : out.retained, ∀ k,
  (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔ qnum.Hchild ≤ A.sides k)
variable (hkernel : Nonempty G) (hcutoff : qnum.Hchild ≤ S.value)
variable (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
variable (hdensity : qnum.δ ≤ Real.exp (-cost)) (hlog : cost + 1 ≤ qnum.v)
variable (hprescribed : cost + 1 ≤ s.Ppres) (hstride : 2 * Real.exp cost ≤ qnum.Ptail)

local notation "input" z => out.denseSliceInput s qnum z (hkeep z) (ActualFixedSpatialForecastPath.commonTuple (path z))
  hkernel hcutoff hlate hdensity le_rfl hlog hprescribed hstride
local notation "member" z => ActualFixedSpatialForecastPath.toDenseSliceMember (path z) (input z)

include ν hpPrep hRprep in

theorem relativePatchSliceConclusion_of_actual_prepared_candidate
    (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
    (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget precision C Ecompare Ptest Rrank Crecovered : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : qnum.capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ qnum.E)
    (hPrecision : actualForecastDataModelRequired localBudget qnum.Pnative qnum.massLog u p ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp qnum.capLog)))
    (hexcess : letI : Nonempty A.Site := A.site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcostSlice : cost ≤ pSlice) (hchartCost : chartCost ≤ pSlice)
    (htest : 2 ≤ pTest)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hσ1 : ∀ j, σ j ≤ 1)
    {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)
    {scoreLog massLogTransfer : ℝ}
    (hTransferMass : 0 ≤ massLogTransfer)
    (hscoreLower : Real.exp (-scoreLog) ≤ outputScore)
    (hmassLower : Real.exp (-massLogTransfer) ≤ outputMass)
    (hU : scoreLog + massLogTransfer + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * qnum.Pnative + 3))
        (2 * u + 4 * p + max 0 qnum.massLog + 20) + 2 +
      massLogTransfer + scoreLog + 8 ≤ Ecompare)
    (hcommonTest : max localBudget (3 * qnum.Pnative + 3) ≤ Ptest)
    (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      s.D (s.D + s.slicedComparisonSourceLog Ptest + 4) (cost + 1)
      (2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14) m))
    (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) (fun j : Fin m => (prep j).space) b R S.value
      (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) a).1)
        ((allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) a).2 : ℝ)) τ)
    (hEprec : 0 ≤ qLate.massLog + Ecompare + 8)
    (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (N i : ℝ))
    (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank ((fun j : Fin m => (prep j).space) j) ((fun j : Fin m => (prep j).poly) j))
    (sampleFn : out.retained → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (readFn : out.retained → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hglobal : ∀ z : out.retained, AllocatedCenteredRecoveredSampleReadAt B (fun j : Fin m => (prep j).space) bW b hb o S hR hσ
      (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1) (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) spatial kernel block Crecovered
      center (path z).center (path z).base (sampleFn z) (readFn z))
    (hcost : 0 ≤ cost) (hE : 0 ≤ Ecompare) (hτ1 : τ ≤ 1)
    (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s
      (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) (2 * Ptest) Ecompare ≤ S.value)
    (hξsmall : ξ ≤ Real.exp (-(2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14)))
    (hEdata : Ecompare + 8 ≤ qLate.E)
    (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
      (Dmod + Fintype.card (Σ j, I j))
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      (Ecompare + 4) (2 * Ptest) s.Pτ) ≤ (N i : ℝ))
    (hprimes : ∀ z, (path z).primes = boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊)
    (hexponent : ∀ z, (path z).exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
    (hbase : ∀ z, (path z).base = z.val.1.val)
    (hnoise : ∀ z, (path z).noise = z.val.2.val)
    (hsample : ∀ z, (path z).sample = sampleFn z z.val.2.val)
    (hread : ∀ z, (path z).read = allocatedReplaceReadNoise B z.val.2.val
      (allocatedJointFrameRead z.val.1.val (readFn z z.val.2.val)))
    (hcenter : ∀ z : out.retained, (path z).center = P.centerLift)
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    (patchCutoff : ℕ) (hPatchCutoff : 0 < patchCutoff)
    (hsmall : 2 / (patchCutoff : ℝ) ≤ 1 / 2)
    {qLog : ℝ}
    (hqLog : ∀ z : out.retained,
      ((member z).slice.path.referenceRetainedCRTModulus patchCutoff : ℝ) ≤ Real.exp qLog)
    {d₀ old removed : ℕ}
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * removed)
    (hremoved : removed ≤ old) (hreturned : d ≤ d₀ + degree * (old - removed))
    {patchCost budget δ ε : ℝ}
    (hPatchCost : relativePatchComplexity patch ≤ patchCost)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (haccuracy : 4 / (patchCutoff : ℝ) ≤ δ)
    (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hFinalBudget : 1 ≤ budget)
    (hRankBudget : ((d₀ + degree * old : ℕ) : ℝ) ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hMatrixBudget : qLog + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hPatchCostBudget : patchCost ≤ budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hScoreBudget : scoreLog ≤ budget)
    (hFinalLarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (N i : ℝ)) :
    RelativePatchSliceConclusion degree N f ((1 - ε) * lam) (d₀ + degree * old)
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  classical
  let : Nonempty A.Site := A.site_nonempty
  obtain ⟨z, hz⟩ := out.exists_actual_shear_buffered_forecast_score
    (s := s) (qnum := qnum) (qLate := qLate) (bW := bW) (ν := ν)
    (patch := patch) (f := f) (lam := lam) (path := path)
    (hkeep := hkeep) (hkernel := hkernel) (hcutoff := hcutoff) (hlate := hlate)
    (hdensity := hdensity) (hlog := hlog) (hprescribed := hprescribed) (hstride := hstride)
    hδlate hHlate hvlate hTaillate hξone hmargin hu hp hbudget hSliceLog hC hCp hCap
    hAccuracy hPrecision hdirect hexcess hSlice hcostSlice hchartCost htest hf hlam
    hσ1 (fun j => (hprep j).1) e hTransferMass hscoreLower hmassLower hU hEcompare
    hcommonTest hσbound hκ hEprec hlarge hRrank hrank sampleFn readFn hglobal hcost hE
    hτ1 hfloor hξsmall hEdata hNgrid hprimes hexponent hbase hnoise hsample hread
  have hc : P.centerLift = (member z).slice.path.center := by
    rw [ActualFixedSpatialForecastPath.toDenseSliceMember_center]
    exact (hcenter z).symm
  have hs := (member z).prepared_shear_buffered_score_of_actual_target
    prep s qnum o bW hb e patch out.ambient P.centerLift hc (fun j => (hprep j).2.1)
    (majorPhasePlateauKernel tagCount) f lam hz
  have hFinalScore : Real.exp (-budget) ≤ outputScore :=
    (Real.exp_le_exp.mpr (neg_le_neg hScoreBudget)).trans hscoreLower
  exact (member z).relativePatchSliceConclusion_of_prepared_shear_score
    prep s qnum o bW hb e hprep hpPrep hRprep hcoord hbW
    patchCutoff hPatchCutoff hsmall (hqLog z) hm hprepared hremoved hreturned
    patch out.ambient hPatchCost f hf hlam hδ haccuracy hε hdiscount hs
    hFinalBudget hRankBudget hDmodBudget hMatrixBudget hPatchCostBudget hcapLog hPnative
    hFinalScore hFinalLarge

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m : ℕ} {G X J₀ : Type} [Fintype G] [Fintype X]
variable (prep : RankPreparationFamily X J₀ m)
variable {preparationP : ℝ} {Rprep : ℕ}
variable (hprep : prep.PreparedHeights preparationP Rprep)
variable (hpPrep : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
variable {I Eout : Fin m → Type} [∀ j, Fintype (I j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod (allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) τ (Real.exp (-cost) / 2))
variable (qnum qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j))
  (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))]
variable (ν : ∀ j, Measure (euclideanSubspace ((fun j : Fin m => (prep j).space) j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (EuclideanJetLayers (fun j : Fin m => (prep j).space) (fun _ : Fin m => Unit))]
variable {stride : X → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) (fun j : Fin m => (prep j).space)}
variable {A : AllocatedExternalCandidateSampler B (fun j : Fin m => (prep j).space) b S hb o hR hσ N (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
  τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem
local instance : Nonempty A.Site := A.site_nonempty
variable {Y : Type} {degree d : ℕ}
variable (patch : PolynomialPatch Y degree d) [Fintype (PolynomialShearIndex patch.weight)]
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost childCost normBudget : ℝ} {rankBound : ℕ}
variable {productive : Finset A.Path}
variable (P : AllocatedExternalCandidateProblem (E := Eout) A
  (polynomialShearNilmanifold patch.weight degree patch.weight_le)
  (RationalTorus.trivialFiltration degree) 0 1
  (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
  chartCost ((A.law.mass productive /
    ((min rankBound ⌊childCost⌋₊ + 1) * (degree + 1) ^ min rankBound ⌊childCost⌋₊ : ℕ)) *
    Real.exp (-normBudget)) (Real.exp (-normBudget)))
variable {gainLog gain pGlobal : ℝ} {netExponent : ℕ}
variable (hchild : 0 ≤ childCost) (hd : d ≤ min rankBound ⌊childCost⌋₊)
  (hchildBudget : childCost ≤ normBudget)
  (hcenters : ∀ i, realPolynomialMass (patch.form.center i) ≤ normBudget)
  (hLip : (patch.kernel.lip : ℝ) ≤ Real.exp normBudget)
  (hgain : Real.exp (-gainLog) ≤ gain)
  (hReady : gain / 16 < A.law.mass productive)
  (hregularityBudget : (normBudget + 2) ^
    allocatedNormalizedShearObservableExponent degree ≤ pGlobal)
  (hpGlobal : 0 ≤ pGlobal) (hchartGlobal : chartCost ≤ pGlobal)
  (hscoreGlobal : normBudget ≤ pGlobal)
  (hmassGlobal : gainLog + 16 + ((degree : ℝ) + 1) * childCost + normBudget ≤ pGlobal)
  (hfGlobal : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
  (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
  (rule : A.DegreeGlobalizationAt (E := Eout) (fun x => ((f x - lam : ℝ) : ℂ))
    degree netExponent pGlobal cost)
variable {δbase PpresBase : ℝ}
variable (path : ∀ _z : P.productive, ActualFixedSpatialForecastPath (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S hR hσ Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B (fun j : Fin m => (prep j).space) b S (fun _ => 0)) (S.value : ℝ) N τ δbase s.P s.Pbad PpresBase)
variable (hkeep : ∀ z : P.productive, ∀ k,
  (P.chart z).keep k ↔ qnum.Hchild ≤ A.sides k)
variable (hkernel : Nonempty G) (hcutoff : qnum.Hchild ≤ S.value)
variable (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
variable (hdensity : qnum.δ ≤ Real.exp (-cost)) (hlog : cost + 1 ≤ qnum.v)
variable (hprescribed : cost + 1 ≤ s.Ppres) (hstride : 2 * Real.exp cost ≤ qnum.Ptail)

include ν hpPrep hRprep hchild hd hchildBudget hcenters hLip hgain hReady
  hregularityBudget hpGlobal hchartGlobal hscoreGlobal hmassGlobal hfGlobal hlam rule
  hkeep hkernel hcutoff hlate hdensity hlog hprescribed hstride in

theorem relativePatchSliceConclusion_of_normalized_prepared_degreeRule
    (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
    (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget precision C Ecompare Ptest Rrank Crecovered : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : qnum.capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ qnum.E)
    (hPrecision : actualForecastDataModelRequired localBudget qnum.Pnative qnum.massLog u p ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp qnum.capLog)))
    (hexcess : letI : Nonempty A.Site := A.site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcostSlice : cost ≤ pSlice) (hchartCost : chartCost ≤ pSlice)
    (htest : 2 ≤ pTest)
    (hσ1 : ∀ j, σ j ≤ 1)
    {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)
    (hU : cost + cost + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * qnum.Pnative + 3))
        (2 * u + 4 * p + max 0 qnum.massLog + 20) + 2 +
      cost + cost + 8 ≤ Ecompare)
    (hcommonTest : max localBudget (3 * qnum.Pnative + 3) ≤ Ptest)
    (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      s.D (s.D + s.slicedComparisonSourceLog Ptest + 4) (cost + 1)
      (2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14) m))
    (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) (fun j : Fin m => (prep j).space) b R S.value
      (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) a).1)
        ((allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) a).2 : ℝ)) τ)
    (hEprec : 0 ≤ qLate.massLog + Ecompare + 8)
    (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (N i : ℝ))
    (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank ((fun j : Fin m => (prep j).space) j) ((fun j : Fin m => (prep j).poly) j))
    (sampleFn : P.productive → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (readFn : P.productive → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hglobal : ∀ z : P.productive, AllocatedCenteredRecoveredSampleReadAt B (fun j : Fin m => (prep j).space) bW b hb o S hR hσ
      (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1) (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) spatial kernel block Crecovered
      center (path z).center (path z).base (sampleFn z) (readFn z))
    (hcost : 0 ≤ cost) (hE : 0 ≤ Ecompare) (hτ1 : τ ≤ 1)
    (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s
      (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) (2 * Ptest) Ecompare ≤ S.value)
    (hξsmall : ξ ≤ Real.exp (-(2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14)))
    (hEdata : Ecompare + 8 ≤ qLate.E)
    (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
      (Dmod + Fintype.card (Σ j, I j))
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      (Ecompare + 4) (2 * Ptest) s.Pτ) ≤ (N i : ℝ))
    (hprimes : ∀ z, (path z).primes = boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊)
    (hexponent : ∀ z, (path z).exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
    (hbase : ∀ z, (path z).base = z.val.1.val)
    (hnoise : ∀ z, (path z).noise = z.val.2.val)
    (hsample : ∀ z, (path z).sample = sampleFn z z.val.2.val)
    (hread : ∀ z, (path z).read = allocatedReplaceReadNoise B z.val.2.val
      (allocatedJointFrameRead z.val.1.val (readFn z z.val.2.val)))
    (hcenter : ∀ z : P.productive, (path z).center = P.centerLift)
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    {ε crtBudget : ℝ} (hεpos : 0 < ε) (hεone : ε ≤ 1)
    (hCRTbudget : 1 ≤ crtBudget) (hCRTinv : ε⁻¹ ≤ crtBudget)
    (hCRTtest : Ptest ∈ Set.Icc 0 crtBudget)
    (hCRTbad : s.Pbad ∈ Set.Icc 0 crtBudget)
    (hCRTpres : s.Ppres ∈ Set.Icc 0 crtBudget)
    {d₀ old removed : ℕ}
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * removed)
    (hremoved : removed ≤ old) (hreturned : d ≤ d₀ + degree * (old - removed))
    {budget : ℝ}
    (hFinalBudget : 1 ≤ budget)
    (hRankBudget : ((d₀ + degree * old : ℕ) : ℝ) ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hMatrixBudget : 2048 * crtBudget ^ 3 + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hPatchCostBudget : 2 * normBudget + 1 ≤ budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hScoreBudget : cost ≤ budget)
    (hFinalLarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (N i : ℝ)) :
    RelativePatchSliceConclusion degree N f ((1 - ε) * lam) (d₀ + degree * old)
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  classical
  let out := P.normalizedShearDegreeConclusion patch
    hchild hd hchildBudget hcenters hLip hgain hReady hregularityBudget
    hpGlobal hchartGlobal hscoreGlobal hmassGlobal hfGlobal hlam rule
  let pathOut := fun z : out.retained => path ⟨z.val, out.subset z.property⟩
  have hkeepOut (z : out.retained) (k) :
      (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔ qnum.Hchild ≤ A.sides k :=
    hkeep ⟨z.val, out.subset z.property⟩ k
  have hNorm : 0 ≤ normBudget := hchild.trans hchildBudget
  have hRank : (d : ℝ) ≤ normBudget :=
    (Nat.cast_le.mpr (hd.trans (min_le_right _ _))).trans
      ((Nat.floor_le hchild).trans hchildBudget)
  have hPatchCost : relativePatchComplexity patch ≤ 2 * normBudget + 1 :=
    relativePatchComplexity_le_of_rank_lip patch hNorm hRank hLip
  obtain ⟨hδ, hcutoffPos, hsmall, haccuracy, hdiscount, _, _⟩ :=
    retainedPatchCutoffChoice_bounds hεpos hεone
  have hqLog := out.returned_modulus_le_exp_discount
    (prep := prep) (hprep := hprep) (s := s) (qnum := qnum)
    (patch := patch) (f := f) (lam := lam)
    (path := pathOut) (hkeep := hkeepOut) (hkernel := hkernel)
    (hcutoff := hcutoff) (hlate := hlate) (hdensity := hdensity)
    (hlog := hlog) (hprescribed := hprescribed) (hstride := hstride)
    hεpos hεone hCRTbudget hCRTinv hCRTtest hCRTbad hCRTpres
    (fun z => hexponent ⟨z.val, out.subset z.property⟩)
  exact out.relativePatchSliceConclusion_of_actual_prepared_candidate
    (prep := prep) (hprep := hprep) (hpPrep := hpPrep) (hRprep := hRprep)
    (s := s) (qnum := qnum) (qLate := qLate) (bW := bW) (ν := ν)
    (patch := patch) (f := f) (lam := lam) (path := pathOut)
    (hkeep := hkeepOut) (hkernel := hkernel) (hcutoff := hcutoff) (hlate := hlate)
    (hdensity := hdensity) (hlog := hlog) (hprescribed := hprescribed) (hstride := hstride)
    (scoreLog := cost) (massLogTransfer := cost)
    hδlate hHlate hvlate hTaillate hξone hmargin hu hp hbudget hSliceLog hC hCp hCap
    hAccuracy hPrecision hdirect hexcess hSlice hcostSlice hchartCost htest
    (fun x _ => hfGlobal x) hlam hσ1 e hcost le_rfl le_rfl hU hEcompare
    hcommonTest hσbound hκ hEprec hlarge hRrank hrank
    (fun z => sampleFn ⟨z.val, out.subset z.property⟩)
    (fun z => readFn ⟨z.val, out.subset z.property⟩)
    (fun z => hglobal ⟨z.val, out.subset z.property⟩)
    hcost hE hτ1 hfloor hξsmall hEdata hNgrid
    (fun z => hprimes ⟨z.val, out.subset z.property⟩)
    (fun z => hexponent ⟨z.val, out.subset z.property⟩)
    (fun z => hbase ⟨z.val, out.subset z.property⟩)
    (fun z => hnoise ⟨z.val, out.subset z.property⟩)
    (fun z => hsample ⟨z.val, out.subset z.property⟩)
    (fun z => hread ⟨z.val, out.subset z.property⟩)
    (fun z => hcenter ⟨z.val, out.subset z.property⟩)
    hcoord hbW (retainedPatchCutoff ε) hcutoffPos hsmall hqLog
    hm hprepared hremoved hreturned hPatchCost hδ haccuracy ⟨hεpos.le, hεone⟩ hdiscount
    hFinalBudget hRankBudget hDmodBudget hMatrixBudget hPatchCostBudget hcapLog hPnative
    hScoreBudget hFinalLarge

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m : ℕ} {G X J₀ : Type} [Fintype G] [Fintype X]
variable (prep : RankPreparationFamily X J₀ m)
variable {preparationP : ℝ} {Rprep : ℕ}
variable (hprep : prep.PreparedHeights preparationP Rprep)
variable (hpPrep : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
variable {I Eout : Fin m → Type} [∀ j, Fintype (I j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable (eSpatial : Fin 2 × X ↪ G)
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod (allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) τ (Real.exp (-cost) / 2))
variable (qnum qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j))
  (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))]
variable (ν : ∀ j, Measure (euclideanSubspace ((fun j : Fin m => (prep j).space) j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (EuclideanJetLayers (fun j : Fin m => (prep j).space) (fun _ : Fin m => Unit))]
variable {stride : X → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) (fun j : Fin m => (prep j).space)}
variable {A : AllocatedExternalCandidateSampler B (fun j : Fin m => (prep j).space) b S hb o hR hσ N (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
  τ ξ stride cells center}

local instance : Nonempty A.Site := A.site_nonempty
variable {degree originalRank D E : ℕ}
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost childCost : ℝ} {productive : Finset A.Path}
variable {gainLog gain pGlobal : ℝ} {netExponent : ℕ}
variable (hchild : 0 ≤ childCost)
  (hgain : Real.exp (-gainLog) ≤ gain)
  (hReady : gain / 16 < A.law.mass productive)
  (hregularityBudget : ((((childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 2) ^
    allocatedNormalizedShearObservableExponent degree ≤ pGlobal)
  (hpGlobal : 0 ≤ pGlobal) (hchartGlobal : chartCost ≤ pGlobal)
  (hscoreGlobal : (((childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤ pGlobal)
  (hmassGlobal : gainLog + 16 + ((degree : ℝ) + 1) * childCost + (((childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤ pGlobal)
  (hfGlobal : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
  (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
  (rule : A.DegreeGlobalizationAt (E := Eout) (fun x => ((f x - lam : ℝ) : ℂ))
    degree netExponent pGlobal cost)
variable (hkernel : Nonempty G) (hcutoff : qnum.Hchild ≤ S.value)
variable (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
variable (hdensity : qnum.δ ≤ Real.exp (-cost)) (hlog : cost + 1 ≤ qnum.v)
variable (hprescribed : cost + 1 ≤ s.Ppres) (hstride : 2 * Real.exp cost ≤ qnum.Ptail)

include ν hpPrep hRprep hchild hgain hReady
  hregularityBudget hpGlobal hchartGlobal hscoreGlobal hmassGlobal hfGlobal hlam rule
  hkernel hcutoff hlate hdensity hlog hprescribed hstride in

theorem relativePatchSliceConclusion_of_normalized_ready

    (centerLift : ∀ j, (prep j).space) (Hinitial : ℕ)
    (hInitialCutoff : Hinitial = qnum.Hchild)
    (hinit : AllocatedNormalizedCandidateConclusion (E := Eout) (A := A)
      degree (fun k => Hinitial ≤ A.sides k) centerLift productive childCost chartCost
      (originalRank + degree * E) f lam)
    (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
    (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget precision C Ecompare Ptest Rrank Crecovered : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : qnum.capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ qnum.E)
    (hPrecision : actualForecastDataModelRequired localBudget qnum.Pnative qnum.massLog u p ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp qnum.capLog)))
    (hexcess : letI : Nonempty A.Site := A.site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcostSlice : cost ≤ pSlice) (hchartCost : chartCost ≤ pSlice)
    (htest : 2 ≤ pTest)
    (hσ1 : ∀ j, σ j ≤ 1)
    {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)
    (hU : cost + cost + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * qnum.Pnative + 3))
        (2 * u + 4 * p + max 0 qnum.massLog + 20) + 2 +
      cost + cost + 8 ≤ Ecompare)
    (hcommonTest : max localBudget (3 * qnum.Pnative + 3) ≤ Ptest)
    (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      s.D (s.D + s.slicedComparisonSourceLog Ptest + 4) (cost + 1)
      (2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14) m))
    (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) (fun j : Fin m => (prep j).space) b R S.value
      (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) a).1)
        ((allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) a).2 : ℝ)) τ)
    (hEprec : 0 ≤ qLate.massLog + Ecompare + 8)
    (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (N i : ℝ))
    (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank ((fun j : Fin m => (prep j).space) j) ((fun j : Fin m => (prep j).poly) j))
    (sampleFn : (X → ℤ) → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (readFn : (X → ℤ) → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hglobal : ∀ base, AllocatedCenteredRecoveredSampleReadAt B (fun j : Fin m => (prep j).space)
      bW b hb o S hR hσ (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
      (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value)
      spatial kernel block Crecovered center centerLift base (sampleFn base) (readFn base))
    (hrecovered : ∀ z ∈ productive, AllocatedCenteredFramedRecoveredSampleAt
      B (fun j : Fin m => (prep j).space) b hb o S hR hσ
      (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
      centerLift z.1.val z.2.val (sampleFn z.1.val z.2.val)
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val)))
    (hgood : let primes := boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊
      letI := actualForecastPrimeNeZero primes (boundedPrimes_prime _)
      ∀ z ∈ productive,
      (∏ p ∈ primes, p ^ largestTestedBadDepth (fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
        (allocatedActualPrimeBad (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value)
          spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val))) ≤
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius (gainLog + 8)))
    (hdet : ∀ z ∈ productive, ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) / 2 <
        |Matrix.det (fun i j : X => spatialMatrixNormalizedEntries eSpatial A.widths z.2.val (t,j,i))|)
    {Pdim Qstride : ℝ}
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
    (hnX : 0 < Fintype.card X) (hgainLog : 0 ≤ gainLog) (hgainDim : gainLog ≤ Pdim)
    (hstrideSource : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hPmodel : preparedCenteredForecastSpatialLog Pdim ≤ s.P)
    (hPbad : 2 * Fintype.card X * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11 ≤ s.Pbad)
    (hcost : 0 ≤ cost) (hE : 0 ≤ Ecompare) (hτ1 : τ ≤ 1)
    (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s
      (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) (2 * Ptest) Ecompare ≤ S.value)
    (hξsmall : ξ ≤ Real.exp (-(2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14)))
    (hEdata : Ecompare + 8 ≤ qLate.E)
    (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
      (Dmod + Fintype.card (Σ j, I j))
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      (Ecompare + 4) (2 * Ptest) s.Pτ) ≤ (N i : ℝ))
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    {ε crtBudget : ℝ} (hεpos : 0 < ε) (hεone : ε ≤ 1)
    (hCRTbudget : 1 ≤ crtBudget) (hCRTinv : ε⁻¹ ≤ crtBudget)
    (hCRTtest : Ptest ∈ Set.Icc 0 crtBudget)
    (hCRTbad : s.Pbad ∈ Set.Icc 0 crtBudget)
    (hCRTpres : s.Ppres ∈ Set.Icc 0 crtBudget)
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * D)
    {budget : ℝ}
    (hFinalBudget : 1 ≤ budget)
    (hRankBudget : childCost + (degree : ℝ) * D ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hMatrixBudget : 2048 * crtBudget ^ 3 + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hPatchCostBudget : 2 * (((childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 1 ≤ budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hScoreBudget : cost ≤ budget)
    (hFinalLarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (N i : ℝ)) :
    RelativePatchSliceConclusion degree N f ((1 - ε) * lam) (originalRank + degree * (D + E))
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  classical
  obtain ⟨d, patch, hd, hreturned, hLip, hcenters, hP⟩ := hinit
  let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
  obtain ⟨P, hsub, hcenterP, hkeepP⟩ := hP
  obtain ⟨hchildBudget, _, _⟩ := allocatedNormalizedBudget_bounds degree
    (Fintype.card (LayerSamplerVariables G I n B)) hchild
  obtain ⟨path, hglobalPath, hprimes, hexponent, hbase, hnoise, hsample, hread, hcenterPath⟩ :=
    exists_allocatedRetainedActualForecastFactory (A := A) bW centerLift sampleFn readFn
      productive P.productive hsub Dmod spatial kernel block eSpatial Pdim gainLog Qstride
      Ptest Crecovered hglobal hrecovered hgood hdet hPdim hX hvars hnX hgainLog hgainDim
      hstrideSource s hPmodel hPbad
  have hkeep (z : P.productive) (k) :
      (P.chart z).keep k ↔ qnum.Hchild ≤ A.sides k := by
    rw [hkeepP z, hInitialCutoff]
  have hRank : ((d + degree * D : ℕ) : ℝ) ≤ budget :=
    (relative_actual_rank_reconstruction_budget hchild hd (le_refl (D : ℝ))).trans hRankBudget
  have hconclusion := P.relativePatchSliceConclusion_of_normalized_prepared_degreeRule
    (prep := prep) (hprep := hprep) (hpPrep := hpPrep) (hRprep := hRprep)
    (s := s) (qnum := qnum) (qLate := qLate) (bW := bW) (ν := ν)
    (patch := patch) (f := f) (lam := lam) (hchild := hchild) (hd := hd)
    (hchildBudget := hchildBudget) (hcenters := hcenters) (hLip := hLip)
    (hgain := hgain) (hReady := hReady) (hregularityBudget := hregularityBudget)
    (hpGlobal := hpGlobal) (hchartGlobal := hchartGlobal) (hscoreGlobal := hscoreGlobal)
    (hmassGlobal := hmassGlobal) (hfGlobal := hfGlobal) (hlam := hlam) (rule := rule)
    (path := path) (hkeep := hkeep) (hkernel := hkernel) (hcutoff := hcutoff)
    (hlate := hlate) (hdensity := hdensity) (hlog := hlog)
    (hprescribed := hprescribed) (hstride := hstride)
    hδlate hHlate hvlate hTaillate hξone hmargin hu hp hbudget hSliceLog hC hCp hCap
    hAccuracy hPrecision hdirect hexcess hSlice hcostSlice hchartCost htest hσ1 e
    hU hEcompare hcommonTest hσbound hκ hEprec hlarge hRrank hrank
    (fun z => sampleFn z.val.1.val) (fun z => readFn z.val.1.val) hglobalPath
    hcost hE hτ1 hfloor hξsmall hEdata hNgrid hprimes hexponent hbase hnoise hsample hread
    (fun z => (hcenterPath z).trans hcenterP.symm) hcoord hbW
    hεpos hεone hCRTbudget hCRTinv hCRTtest hCRTbad hCRTpres
    (d₀ := d) (old := D) (removed := D) hm hprepared le_rfl (by simp)
    hFinalBudget hRank hDmodBudget hMatrixBudget hPatchCostBudget hcapLog hPnative
    hScoreBudget hFinalLarge
  apply hconclusion.mono _ le_rfl
  apply relative_actual_rank_reconstruction_le (removed := D) (by omega)
  simpa using hreturned

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m M nX Jalloc : ℕ} {J₀ : Type}
variable (prep : RankPreparationFamily (Fin nX) J₀ m)
variable {preparationP : ℝ} {Rprep : ℕ}
variable (hprep : prep.PreparedHeights preparationP Rprep)
variable (hpPrep : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m Jalloc)) (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Lrank : ℕ} {spatial : Fin Lrank ↪ (EnlargedPreparedCommonKernel m Jalloc)}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ (EnlargedPreparedCommonKernel m Jalloc)}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ (EnlargedPreparedCommonSamplerBlock prep Jalloc) ⟨j,a.val⟩}
variable (eSpatial : Fin 2 × (Fin nX) ↪ (EnlargedPreparedCommonKernel m Jalloc))
variable {gainLog : ℝ}
variable {N : (Fin nX) → ℕ} {ξ cost : ℝ}
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable {o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j))
  (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))]
variable (ν : ∀ j, Measure (euclideanSubspace ((fun j : Fin m => (prep j).space) j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (EuclideanJetLayers (fun j : Fin m => (prep j).space) (fun _ : Fin m => Unit))]
variable {stride : (Fin nX) → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc))) (Fin nX) stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) (fun j : Fin m => (prep j).space)}
variable {A : AllocatedExternalCandidateSampler (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space) b S hb o hR hσ N (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
  (Real.exp (-(gainLog + (nX : ℝ) + 8))) ξ stride cells center}

local instance : Nonempty A.Site := A.site_nonempty
variable {degree originalRank D E : ℕ}
variable (f : ((Fin nX) → ℤ) → ℝ) (lam : ℝ)
variable {chartCost childCost : ℝ} {productive : Finset A.Path}
variable {gain pGlobal : ℝ} {netExponent : ℕ}
variable (hchild : 0 ≤ childCost)
  (hgain : Real.exp (-gainLog) ≤ gain)
  (hReady : gain / 16 < A.law.mass productive)
  (hregularityBudget : ((((childCost + (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 2) ^
    allocatedNormalizedShearObservableExponent degree ≤ pGlobal)
  (hpGlobal : 0 ≤ pGlobal) (hchartGlobal : chartCost ≤ pGlobal)
  (hscoreGlobal : (((childCost + (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤ pGlobal)
  (hmassGlobal : gainLog + 16 + ((degree : ℝ) + 1) * childCost + (((childCost + (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤ pGlobal)
  (hfGlobal : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
  (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
  (rule : A.DegreeGlobalizationAt (E := Eout) (fun x => ((f x - lam : ℝ) : ℂ))
    degree netExponent pGlobal cost)
variable {pRadius Qstride PF Pchart childLog Pdim : ℝ}

include ν hpPrep hRprep hchild hgain hReady hregularityBudget
  hpGlobal hchartGlobal hscoreGlobal hmassGlobal hfGlobal hlam rule in

theorem relativePatchSliceConclusion_of_prepared_source_geometry

    (hmPositive : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace ((prep j).space)) (b j) ≤ Real.exp Pchart)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (prep j)), ‖normalizedOrthogonalChart (euclideanSubspace ((prep j).space)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace ((prep j).space) × (Fin (preparedSamplerTransverse prep j) → ℝ)),
      ‖(normalizedOrthogonalChart (euclideanSubspace ((prep j).space)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    {Cdetect : ℕ} {Bstruct Pscale Dgeometry target Pk Prho pDetect aDetect detectionGain : ℝ}
    (hInverseBound : ∀ j, inverse j ≤ Real.exp Bstruct)
    (hgeometry : PreparedUniformDegreeGeometryAt
      (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space) b S 0 Cdetect nX
      Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain)
    (hchildLog : 0 ≤ childLog)

    (centerLift : ∀ j, (prep j).space)
    (hinit : AllocatedNormalizedCandidateConclusion (E := Eout) (A := A)
      degree (fun k => (preparedSlicedForecastChildSize childLog) ≤ A.sides k) centerLift productive childCost chartCost
      (originalRank + degree * E) f lam)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin (Real.exp (-(gainLog + (nX : ℝ) + 8))) N x ≤ N x)
    {u p pSlice pTest localBudget precision C Ecompare Ptest Rrank Crecovered : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : (preparedConcreteSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog) ≤ p)
    (hPrecision : actualForecastDataModelRequired localBudget (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (2 * u + 4 * p + 12)) (preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog (2 * u + 4 * p + 12)) u p ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)))) C (Real.exp (preparedConcreteSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog))))
    (hexcess : letI : DecidableEq (Fin nX) := Classical.decEq _
      letI : Nonempty A.Site := A.site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcostSlice : cost ≤ pSlice) (hchartCost : chartCost ≤ pSlice)
    (htest : 2 ≤ pTest)
    {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)
    (hU : cost + cost + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (2 * u + 4 * p + 12)) + 3))
        (2 * u + 4 * p + max 0 (preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog (2 * u + 4 * p + 12)) + 20) + 2 +
      cost + cost + 8 ≤ Ecompare)
    (hcommonTest : max localBudget (3 * (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (2 * u + 4 * p + 12)) + 3) ≤ Ptest)
    (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)) ((allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)) + (preparedSlicedForecastSourceLog m M Jalloc Ptest) + 4) (cost + 1)
      (2 * (preparedSlicedForecastSourceLog m M Jalloc Ptest) + (Ecompare + 4) + 14) m))
    (hlarge : ∀ i, Real.exp ((max (max (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost) (2 * max Ptest (3 * (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (Ecompare + 8)) + 3) + 1))
      ((preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog (Ecompare + 8)) + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (N i : ℝ))
    (hRrank : Real.exp ((max (max (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost) (2 * max Ptest (3 * (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (Ecompare + 8)) + 3) + 1))
      ((preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog (Ecompare + 8)) + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank ((fun j : Fin m => (prep j).space) j) ((fun j : Fin m => (prep j).poly) j))
    (sampleFn : ((Fin nX) → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) × (Fin nX) → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
    (readFn : ((Fin nX) → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) × (Fin nX) → ℤ) →
      AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m Jalloc) (Fin nX) (PreparedSamplerContinuous prep) Eout (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc) → ℤ)
    (hglobal : ∀ base, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space)
      bW b hb o S hR hσ (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
      (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) (fun j : Fin m => (prep j).space) b S.value)
      spatial kernel block Crecovered center centerLift base (sampleFn base) (readFn base))
    (hrecovered : ∀ z ∈ productive, AllocatedCenteredFramedRecoveredSampleAt
      (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space) b hb o S hR hσ
      (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
      centerLift z.1.val z.2.val (sampleFn z.1.val z.2.val)
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val)))
    (hgood : let primes := boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊
      letI := actualForecastPrimeNeZero primes (boundedPrimes_prime _)
      ∀ z ∈ productive,
      (∏ p ∈ primes, p ^ largestTestedBadDepth (fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
        (allocatedActualPrimeBad (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) (fun j : Fin m => (prep j).space) b S.value)
          spatial kernel block primes (modularForecastRankConstant m (nX + m * M) : ℝ)) p
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val))) ≤
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius (gainLog + 8)))
    (hdet : ∀ z ∈ productive, ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card (Fin nX)) (jointSpatialError gainLog) / 2 <
        |Matrix.det (fun i j : (Fin nX) => spatialMatrixNormalizedEntries eSpatial A.widths z.2.val (t,j,i))|)
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card (Fin nX) : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) ≤ Pdim)
    (hnX : 0 < Fintype.card (Fin nX)) (hgainDim : gainLog ≤ Pdim)
    (hstrideSource : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hE : 0 ≤ Ecompare)
    (hSourceFloor : preparedSlicedForecastCommonFloor 0
      childLog cost (preparedSlicedForecastComparisonFloorLog m M nX Jalloc
        ((nX + m * M) + Fintype.card (Σ j, (PreparedSamplerContinuous prep) j)) Pdim cost pRadius gainLog Qstride Ptest (2 * Ptest) Ecompare) ≤ S.value)
    (hξsmall : ξ ≤ Real.exp (-(2 * (preparedSlicedForecastSourceLog m M Jalloc Ptest) + (Ecompare + 4) + 14)))
    (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
      ((nX + m * M) + Fintype.card (Σ j, (PreparedSamplerContinuous prep) j))
      (preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest)
      (Ecompare + 4) (2 * Ptest) (gainLog + nX + 8)) ≤ (N i : ℝ))
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    {ε crtBudget : ℝ} (hεpos : 0 < ε) (hεone : ε ≤ 1)
    (hCRTbudget : 1 ≤ crtBudget) (hCRTinv : ε⁻¹ ≤ crtBudget)
    (hCRTtest : Ptest ∈ Set.Icc 0 crtBudget)
    (hCRTbad : (preparedSlicedForecastBadLog m nX Qstride gainLog) ∈ Set.Icc 0 crtBudget)
    (hCRTpres : (cost + 1) ∈ Set.Icc 0 crtBudget)
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * D)
    {budget : ℝ}
    (hFinalBudget : 1 ≤ budget)
    (hRankBudget : childCost + (degree : ℝ) * D ≤ budget)
    (hDmodBudget : ((nX + m * M) : ℝ) ≤ budget)
    (hMatrixBudget : 2048 * crtBudget ^ 3 + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hPatchCostBudget : 2 * (((childCost + (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 1 ≤ budget)
    (hcapLog : (preparedConcreteSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog) ≤ budget) (hPnative : (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (2 * u + 4 * p + 12)) ≤ budget)
    (hScoreBudget : cost ≤ budget)
    (hFinalLarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (N i : ℝ)) :
    RelativePatchSliceConclusion degree N f ((1 - ε) * lam) (originalRank + degree * (D + E))
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  classical
  let s := preparedActualSlicedForecastSetupOfSourceGeometry (nX := nX) prep Jalloc (fun j : Fin m => (prep j).space) b o S bW hb
    hmPositive hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound inverse hinverse hchart hInverseBound hgeometry
  obtain ⟨qnum, hqδ, hqH, hqv, hqTail, hqE, hqPN, hqMass, hqCap, hqCtail,
      hqT, hqMass0, hqCap0, hqPN0⟩ :=
    exists_preparedSourceSlicedForecastNumerics (nX := nX) prep Jalloc (fun j : Fin m => (prep j).space) b o S bW hb
    hmPositive hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound inverse hinverse hchart hInverseBound hgeometry
      childLog (2 * u + 4 * p + 12) hchildLog (by linarith)
  obtain ⟨qLate, hlδ, hlH, hlv, hlTail, hlE, hlPN, hlMass, hlCap, hlCtail,
      hlT, hlMass0, hlCap0, hlPN0⟩ :=
    exists_preparedSourceSlicedForecastNumerics (nX := nX) prep Jalloc (fun j : Fin m => (prep j).space) b o S bW hb
    hmPositive hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound inverse hinverse hchart hInverseBound hgeometry
      childLog (Ecompare + 8) hchildLog (by linarith)
  obtain ⟨hsP, hsScale, hsBad, hsPres, hsPκ, hsκ, hsCap, hsPτ, hsPK, hsPF, hsD⟩ :=
    preparedActualSlicedForecastSetupOfSourceGeometry_scalar_values (nX := nX) prep Jalloc (fun j : Fin m => (prep j).space) b o S bW hb
    hmPositive hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound inverse hinverse hchart hInverseBound hgeometry
  obtain ⟨hsPcap, hsPu, hsGrid, hsFloor, hsPerturb, hsCommon⟩ :=
    preparedActualSlicedForecastSetupOfSourceGeometry_comparison_data (nX := nX) prep Jalloc (fun j : Fin m => (prep j).space) b o S bW hb
    hmPositive hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound inverse hinverse hchart hInverseBound hgeometry
      ((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j))
      Ptest (2 * Ptest) Ecompare (mul_nonneg (by norm_num) hCRTtest.1) hE
  change s.pcap = preparedSlicedForecastPrimitiveCap at hsPcap
  change s.P = preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost at hsP
  change s.Pbad = preparedSlicedForecastBadLog m nX Qstride gainLog at hsBad
  change s.Ppres = cost + 1 at hsPres
  change s.Pτ = gainLog + nX + 8 at hsPτ
  change s.D = allocatedComparisonDimension m
    (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) at hsD
  change s.κ = forecastGeometricJacobian (X := Fin nX)
    (I := PreparedSamplerContinuous prep) (fun j : Fin m => (prep j).space) b R S.value
    (preparedForecastGridVolume prep Jalloc (fun j : Fin m => (prep j).space) b S)
    (Real.exp (-(gainLog + (nX : ℝ) + 8))) at hsκ
  change s.slicedComparisonSourceLog Ptest =
    preparedSlicedForecastSourceLog m M Jalloc Ptest at hsPu
  change ActualFixedSpatialSlicedForecastPath.comparisonGridLog s
    (s.slicedComparisonSourceLog Ptest) =
    preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest at hsGrid
  let periodLog : ℝ := 0
  let comparisonLog := preparedSlicedForecastComparisonFloorLog m M nX Jalloc
    ((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j))
    Pdim cost pRadius gainLog Qstride Ptest (2 * Ptest) Ecompare
  have hSourceFloor' : preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog ≤ S.value :=
    hSourceFloor
  have hfloorBounds := preparedSlicedForecastCommonFloor_bounds periodLog childLog cost comparisonLog
  have hcutoff : qnum.Hchild ≤ S.value := by
    rw [hqH]
    exact hfloorBounds.2.2.2.1.trans hSourceFloor'
  have h2S : 2 * Real.exp cost ≤ (S.value : ℝ) :=
    hfloorBounds.2.2.2.2.1.trans (Nat.cast_le.mpr hSourceFloor')
  have hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ) := by
    have h := mul_le_mul_of_nonneg_left h2S (Real.exp_nonneg (-cost))
    have heq : Real.exp (-cost) * (2 * Real.exp cost) = 2 := by
      rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    exact heq ▸ h
  have hdet' := hdet
  have hdecX : instDecidableEqFin nX =
      (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  rw [hdecX] at hdet'
  have hdirect' := @hdirect
  rw [hdecX] at hdirect'
  exact relativePatchSliceConclusion_of_normalized_ready
    (prep := prep) (hprep := hprep) (hpPrep := hpPrep) (hRprep := hRprep)
    (eSpatial := eSpatial) (s := s) (qnum := qnum) (qLate := qLate) (bW := bW) (ν := ν)
    (f := f) (lam := lam) (hchild := hchild) (hgain := hgain) (hReady := hReady)
    (hregularityBudget := hregularityBudget) (hpGlobal := hpGlobal)
    (hchartGlobal := hchartGlobal) (hscoreGlobal := hscoreGlobal) (hmassGlobal := hmassGlobal)
    (hfGlobal := hfGlobal) (hlam := hlam) (rule := rule)
    (hkernel := ⟨enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m) 0⟩)
    (hcutoff := hcutoff) (hlate := hlate)
    (hdensity := by rw [hqδ]; exact le_rfl)
    (hlog := hqv.symm.le) (hprescribed := hsPres.symm.le)
    (hstride := by rw [hqTail]; exact preparedSlicedForecastTailCap_stride_le cost)
    centerLift (preparedSlicedForecastChildSize childLog) hqH.symm hinit
    (hqδ.trans hlδ.symm) (hqH.trans hlH.symm) (hqv.trans hlv.symm) (hqTail.trans hlTail.symm)
    hξone hmargin hu hp hbudget hSliceLog hC hCp
    (by simpa only [hqCap] using hCap) hqE.symm.le
    (by simpa only [hqPN, hqMass] using hPrecision)
    (by rw [hqCap]; exact @hdirect') hexcess hSlice hcostSlice hchartCost htest hσone e
    hU (by simpa only [hqPN, hqMass] using hEcompare)
    (by simpa only [hqPN] using hcommonTest)
    (by simpa only [ActualFixedSpatialForecastSetup.slicedComparisonSourceLog, hsD, hsPcap,
      preparedSlicedForecastSourceLog, pow_two] using hσbound)
    (by
      apply hsκ.trans
      unfold preparedForecastGridVolume preparedActualForecastGridVolume
      congr 1)
    (by linarith [hlMass0])
    (by simpa only [hsP, hlPN, hlMass] using hlarge)
    (by simpa only [hsP, hlPN, hlMass] using hRrank) hrank
    sampleFn readFn hglobal hrecovered hgood hdet'
    hPdim hX hvars hnX hGain hgainDim hstrideSource
    (by rw [hsP]; exact (le_max_left _ _).trans (le_max_right _ _))
    (by simp only [hsBad, preparedSlicedForecastBadLog, Fintype.card_fin]; exact le_rfl)
    hcost hE (Real.exp_le_one_iff.mpr (by have := Nat.cast_nonneg (α := ℝ) nX; linarith))
    ((hsCommon periodLog childLog).trans hSourceFloor')
    (by simpa only [ActualFixedSpatialForecastSetup.slicedComparisonSourceLog, hsD, hsPcap,
      preparedSlicedForecastSourceLog, pow_two] using hξsmall) hlE.symm.le
    (by simpa only [ActualFixedSpatialSlicedForecastPath.comparisonGridLog,
      ActualFixedSpatialForecastSetup.slicedComparisonSourceLog, hsD, hsPcap, hsP, hsBad, hsPres,
      hsPτ, preparedSlicedForecastSourceLog, preparedSlicedForecastGridLog, Fintype.card_fin, pow_two] using hNgrid) hcoord hbW
    hεpos hεone hCRTbudget hCRTinv hCRTtest
    (by simpa only [hsBad] using hCRTbad) (by simpa only [hsPres] using hCRTpres)
    hm hprepared hFinalBudget hRankBudget
    (by simpa only [Nat.cast_add, Nat.cast_mul] using hDmodBudget) hMatrixBudget hPatchCostBudget
    (by simpa only [hqCap] using hcapLog) (by simpa only [hqPN] using hPnative)
    hScoreBudget hFinalLarge

end Erdos3.VectorPolynomial

end

end OAI

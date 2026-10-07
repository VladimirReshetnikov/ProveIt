import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateForecastComparisonSource

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}
variable (qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
variable (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ δbase s.P s.Pbad PpresBase)

namespace AllocatedExternalCandidateProblem.Conclusion

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ)

variable {E Ptest : ℝ}
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + (s.slicedComparisonSourceLog Ptest) + 4) (cost + 1) (2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14) m))
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)

variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ qLate.massLog + E + 8)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center path.center path.base sampleFn readFn)

variable (hcost : 0 ≤ cost) (hE : 0 ≤ E)
variable (hτ1 : τ ≤ 1)
variable (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) (2 * Ptest) E ≤ S.value)
variable (hξsmall : ξ ≤ Real.exp (-(2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ qLate.E)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
  (E + 4) (2 * Ptest) s.Pτ) ≤ (physicalN i : ℝ))

variable {earlyPnative earlyMassLog earlyCapLog earlyEdata : ℝ}
variable (earlyData : ActualForecastData physicalN originalpoly
  earlyPnative earlyMassLog earlyCapLog earlyEdata)
variable (hEarlyCenter : earlyData.centerConstant = fun j => (path.center j).val)

variable (hprimes : path.primes = boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊)
variable (hexponent : path.exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)

variable {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ physicalN originalpoly hmem
      τ ξ stride cells center)
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {r d t : ℕ} {D : RationalFilteredNilmanifold L r d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {chartCost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := Eout) A D Fmark φ marked observable weight
      chartCost massThreshold scoreThreshold}
    {outputMass outputScore : ℝ}
    (out : P.Conclusion cost outputMass outputScore)
    (z : out.retained)
    (hkeep : ∀ k, (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔
      qnum.Hchild ≤ A.sides k)
    (hkernel : Nonempty G)
    (hcutoff : qnum.Hchild ≤ S.value)
    (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
    (hdensity : qnum.δ ≤ Real.exp (-cost))
    (hlog : cost + 1 ≤ qnum.v)
    (hprescribed : cost + 1 ≤ s.Ppres)
    (hstride : 2 * Real.exp cost ≤ qnum.Ptail)
    (hbase : path.base = z.val.1.val)
    (hnoise : path.noise = z.val.2.val)
    (hsample : path.sample = sampleFn z.val.2.val)
    (hread : path.read = allocatedReplaceReadNoise B z.val.2.val
      (allocatedJointFrameRead z.val.1.val (readFn z.val.2.val)))

local notation "candidateInput" => out.denseSliceInput s qnum z hkeep path.commonTuple
  hkernel hcutoff hlate hdensity le_rfl hlog hprescribed hstride

include hR hσ hdegree hσbound ν hlattice hcompact hmargin hκ hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hcost hE hτ1 hfloor hξsmall hEdata hNgrid
  hEarlyCenter hδlate hHlate hvlate hTaillate hprimes hexponent
  hbase hnoise hsample hread in

theorem denseSliceInput_ambient_bounded_original_twist_precision :
    let input := candidateInput
    earlyData.target = (path.toDenseSliceMember input).slice.target
      (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb originalpoly hmem s.κ →
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun site => W.eval physicalN originalpoly
          (fun a => path.base a + integerPhysicalSite site.val path.noise a)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) A.integerBox_nonempty).complexMean
        (fun u => W.eval physicalN originalpoly u.val * earlyData.target u)‖ ≤ Real.exp (-E) := by
  intro input hTarget
  have hcost_match : input.cost = cost :=
    out.denseSliceInput_cost s qnum z hkeep path.commonTuple
      hkernel hcutoff hlate hdensity le_rfl hlog hprescribed hstride
  exact forecastFiber_ambient_bounded_original_twist_precision
    (cost := cost) (E := E) (Ptest := Ptest) (Rrank := Rrank)
    (periodCap := periodCap) (coverCap := coverCap) (Lip := Lip)
    (input := input) (hcost_match := hcost_match)
    (s := s) (path := path) (hb := hb) (o := o) (originalpoly := originalpoly) (hmem := hmem) (ξ := ξ) (A := A) (out := out) (z := z)
    (qnum := qnum) (qLate := qLate) (hδlate := hδlate) (hHlate := hHlate)
    (hvlate := hvlate) (hTaillate := hTaillate) (bW := bW) (W := W)
    (hdegree := hdegree) (hσbound := hσbound) (ν := ν) (hmargin := hmargin)
    (hκ := hκ) (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (C := C) (hglobal := hglobal) (hcost := hcost) (hE := hE) (hτ1 := hτ1)
    (hfloor := hfloor) (hξsmall := hξsmall) (hEdata := hEdata) (hNgrid := hNgrid)
    (earlyData := earlyData) (hEarlyCenter := hEarlyCenter) (hTarget := hTarget)
    (hprimes := hprimes) (hexponent := hexponent)
    (hbase := hbase) (hnoise := hnoise) (hsample := hsample) (hread := hread)

include hR hσ hdegree hσbound ν hlattice hcompact hmargin hκ hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hcost hE hτ1 hfloor hξsmall hEdata hNgrid
  hEarlyCenter hδlate hHlate hvlate hTaillate hprimes hexponent
  hbase hnoise hsample hread in

theorem siteLaw_ambient_bounded_original_twist_precision :
    let input := candidateInput
    earlyData.target = (path.toDenseSliceMember input).slice.target
      (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb originalpoly hmem s.κ →
    ‖(out.siteLaw z).complexMean
        (fun site => W.eval physicalN originalpoly (A.physical z.val site)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) A.integerBox_nonempty).complexMean
        (fun u => W.eval physicalN originalpoly u.val * earlyData.target u)‖ ≤ Real.exp (-E) := by
  intro input hTarget
  have hcost_match : input.cost = cost :=
    out.denseSliceInput_cost s qnum z hkeep path.commonTuple
      hkernel hcutoff hlate hdensity le_rfl hlog hprescribed hstride
  rw [← denseSliceInput_physical_complexMean (s := s) (path := path) (hb := hb) (o := o) (originalpoly := originalpoly) (hmem := hmem) (ξ := ξ) (A := A) (out := out) (z := z) (qnum := qnum) (hkeep := hkeep)
    (hkernel := hkernel) (hcutoff := hcutoff) (hlate := hlate) (hdensity := hdensity)
    (hlog := hlog) (hprescribed := hprescribed) (hstride := hstride)
    (hbase := hbase) (hnoise := hnoise)]
  exact forecastFiber_ambient_bounded_original_twist_precision
    (cost := cost) (E := E) (Ptest := Ptest) (Rrank := Rrank)
    (periodCap := periodCap) (coverCap := coverCap) (Lip := Lip)
    (input := input) (hcost_match := hcost_match)
    (s := s) (path := path) (hb := hb) (o := o) (originalpoly := originalpoly) (hmem := hmem) (ξ := ξ) (A := A) (out := out) (z := z)
    (qnum := qnum) (qLate := qLate) (hδlate := hδlate) (hHlate := hHlate)
    (hvlate := hvlate) (hTaillate := hTaillate) (bW := bW) (W := W)
    (hdegree := hdegree) (hσbound := hσbound) (ν := ν) (hmargin := hmargin)
    (hκ := hκ) (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (C := C) (hglobal := hglobal) (hcost := hcost) (hE := hE) (hτ1 := hτ1)
    (hfloor := hfloor) (hξsmall := hξsmall) (hEdata := hEdata) (hNgrid := hNgrid)
    (earlyData := earlyData) (hEarlyCenter := hEarlyCenter) (hTarget := hTarget)
    (hprimes := hprimes) (hexponent := hexponent)
    (hbase := hbase) (hnoise := hnoise) (hsample := hsample) (hread := hread)

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI

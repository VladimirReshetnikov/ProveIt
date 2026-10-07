import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeOrdinaryTerminal

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree realGradedSymbolPolynomial

noncomputable section

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type} {Pivot : Type} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG (s + 1) d₀}
    {dMark : ℕ} {Mmark : RationalFilteredNilmanifold LM (s + 1) dMark} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Mmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Mmark.filtration φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (keepLong : LayerSamplerVariables G I n B → Prop)
    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

variable (js : List Pivot) {dQ : ℕ}
    (Q : RationalFilteredNilmanifold
      (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) (s + 1) dQ)
    (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
    (hker : ∀ z ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ z = 0)

local notation "LQuot" => LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js

variable
    {pGeometry adaptedBudget markInput markBudget : ℝ}
    (geometry : (optionProduct D (fun j => (F.native j).model)).AdaptedMapGeometryData
      (optionProduct Q (fun j => (F.native j).model))
      (optionMarkedLieMap (L := fun j => (F.native j).L)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))) ((pGeometry + 3) ^ 2) adaptedBudget)
    (markGeometry : (optionProduct Q (fun j => (F.native j).model)).FixedSourceAdaptedMarkGeometryData
      (optionProduct Mmark (fun j => (F.native j).model)) geometry.target
      (optionMarkedLieMap (L := fun j => (F.native j).L)
        (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker))
      markInput markBudget)

variable {scheduleExponent Cprimitive : ℕ} {x qVertical qCommon pProj : ℝ}

local notation "fullBudget" => nativePhysicalTerminalFullBudget
  (s + 1) m Cprimitive scheduleExponent x
local notation "affineBudget" => nativePhysicalTerminalAffineBudget (s + 1) scheduleExponent x
local notation "ordinaryBudget" => candidatePhysicalOrdinaryBudget fullBudget
local notation "backendBudget" => allocatedAffineCanonicalBudget s ordinaryBudget fullBudget
local notation "separation" => Real.exp (candidatePrimitiveFreezingCutoff s 1 backendBudget)
local notation "recursiveBudget" => finiteFreezingRecursiveParameter
  (candidatePrimitivePhysicalBudgetExponent s 1) backendBudget
local notation "factorMass" => Real.exp (-(verticalDecompositionBudget qVertical *
  Fintype.card Pivot + ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H

theorem conclusion_of_actualAdaptedPivotQuotientLongPhysicalTerminal
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ Mmark.filtration.layer k)
    (hsurj : ∀ k, ∀ y ∈ Mmark.filtration.layer k,
      ∃ z ∈ D.filtration.layer k, φ z = y)
    (hx : 0 ≤ x)
    (hgeometry : adaptedBudget ≤ fullBudget) (hmark : markBudget ≤ fullBudget)
    (hjoint : (pGeometry + 3) ^ 2 ≤ fullBudget)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ fullBudget)
    (hprojection : (pProj + 2) ^ 4 ≤ fullBudget)
    (hfactor : (pProj + 2) ^ 3 + qCommon ≤ fullBudget)
    (hcost : cost ≤ fullBudget)
    (hshort : ∀ i, ¬keepLong i → (A.sides i : ℝ) ≤ Real.exp fullBudget)
    (hweight : ∀ y, ‖weight y‖ ≤ Real.exp fullBudget)
    (hscoreBound : Real.exp (-fullBudget) ≤ scoreThreshold)
    (hmassBound : Real.exp (-fullBudget) ≤ factorMass)
    {e : ℕ}
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := Deck) weight s
      (refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2) recursiveBudget outputCost)
    (houtput : recursiveBudget ≤ outputCost) :
    ∀ [TopologicalSpace (ℝ ⊗[ℚ] LQuot)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LQuot)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LQuot)] [T2Space (ℝ ⊗[ℚ] LQuot)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQuot (fun j => (F.native j).L) i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQuot (fun j => (F.native j).L) i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQuot (fun j => (F.native j).L) i))] [T2Space (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQuot (fun j => (F.native j).L) i))]
    (descendedTests : (X → ℤ) → Q.Niltest (fullTaggedVariableWeight (X := X) J))
    (hrecovery : ∀ x (g : D.RealGroup),
      (descendedTests x).observable (QuotientGroup.mk
        (realificationMap (L := LG) (M := LQuot) (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
        (observable : (X → ℤ) → D.Space → ℂ) x (QuotientGroup.mk g))
    (hpGeometry : 0 ≤ pGeometry) (hQgeometry : Q.GeometryComplexityLE pGeometry)
    (hunit : ∀ y, (descendedTests y).UnitIntervalValued)
    (hcomplexity : ∀ y, (descendedTests y).ComplexityLE pGeometry)
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((fullBudget + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ y ∈ integerBox N, ∃ i, ∀ z,
          ‖(fun x => (descendedTests x).observable) y z - (fun x => (descendedTests x).observable) (centers i).val z‖ ≤ accuracy),
    let hmarkΦ := D.nativeOptionFixedSourceQuotientMark_mem_layer Mmark
      (D.filtration.pivotAnnihilatorIdeal φ F.η js)
      (by rw [D.filtration.terminal]; exact bot_le) Q hQ
      (fun j => (F.native j).model) φ hker hφ geometry.target
    F.ActualAdaptedPivotQuotientLongPhysicalTerminal keepLong H sourceCenter hpath hcenter hfrozen
      observable weight scoreThreshold hscore geometry.source.basis geometry.source.weight
      geometry.source.layers js Q hQ hker (fun x => (descendedTests x).observable) hrecovery geometry.target
      markGeometry.target.basis markGeometry.target.weight
      (Mmark.optionAdaptedModel_layers (fun j => (F.native j).model) markGeometry.target) hmarkΦ
      scheduleExponent Cprimitive x separation qVertical qCommon pProj →
    ∃ (retained : Finset A.Path) (hsub : retained ⊆ H)
      (hmass : factorMass ≤ A.law.mass retained),
      0 < A.law.mass retained ∧
      let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
        scoreThreshold hscore retained hsub hmass
      let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker (fun x => (descendedTests x).observable) hrecovery geometry.target
      Nonempty (target.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  classical
  intro _ _ _ _ _ _ _ _ descendedTests hrecovery hpGeometry hQgeometry hunit hcomplexity hnet
    hmarkΦ hterminal
  obtain ⟨ha, hw, hpFull⟩ :=
    nativePhysicalTerminalBudgets_nonneg (s + 1) m Cprimitive scheduleExponent hx
  have hcenterBudget : certifiedAffineCenterBudget affineBudget ≤ fullBudget :=
    (allocatedCandidateTerminalFullInput_bounds (s + 1) m Cprimitive hx hw ha).2.2.2.2.2.2.1
  have hordinary := candidatePhysicalOrdinaryBudget_bounds hpFull
  have hscalar := hordinary.2.1
  obtain ⟨retained, hsub, hmass, hpos, packet⟩ :=
    F.ordinaryData_of_actualAdaptedPivotQuotientLongPhysicalTerminal keepLong H sourceCenter
      hpath hcenter hfrozen observable weight scoreThreshold hscore js Q hQ hker (fun x => (descendedTests x).observable)
      hrecovery geometry markGeometry hφ hsurj hordinary.1
      (hgeometry.trans hscalar) (hmark.trans hscalar) (hjoint.trans hscalar)
      (hvariables.trans hscalar) (hprojection.trans hscalar) (hfactor.trans hscalar)
      (hcost.trans hscalar)
      (fun i hi => (hshort i hi).trans (Real.exp_le_exp.mpr hscalar)) hterminal
  obtain ⟨packet⟩ := packet
  obtain ⟨hpositive, _hnorm, hLip, hnetTransfer⟩ :=
    geometry.optionTarget_observable_regularity Q (fun j => (F.native j).model)
      descendedTests hpGeometry hQgeometry hunit hcomplexity
  have hnet' := hnetTransfer (integerBox N)
    (fun accuracy => Real.exp ((fullBudget + Real.log (1 / accuracy) + e) ^ e)) hnet
  refine ⟨retained, hsub, hmass, hpos, ?_⟩
  apply packet.conclusion_of_bounds rfl F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall F.hpoly
    (fun y => (hweight y).trans (Real.exp_le_exp.mpr hscalar))
    ((Real.exp_le_exp.mpr (neg_le_neg hscalar)).trans hscoreBound)
    (candidatePhysicalOrdinaryBudget_mass hpFull ha hcenterBudget hmassBound)
    F.hξ ⟨Real.exp (nativeOptionTargetObservableBudget pGeometry), Real.exp_nonneg _⟩
    (Real.exp_le_exp.mpr (candidatePhysicalOrdinaryBudget_observable hpFull hjoint))
    hLip hpositive ?_ outputCost lowerIH houtput
  intro accuracy haccuracy haccuracy1
  obtain ⟨count, hcount, centers, hcenters⟩ := hnet' accuracy haccuracy haccuracy1
  refine ⟨count, hcount.trans ?_, centers, hcenters⟩
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log (1 / accuracy) :=
    Real.log_nonneg ((one_le_div haccuracy).mpr haccuracy1)
  exact pow_le_pow_left₀ (by positivity) (by linarith only [hscalar]) e

end AllocatedExternalCandidateSpatialNativeFamily
end
end Erdos3.VectorPolynomial

end

end OAI

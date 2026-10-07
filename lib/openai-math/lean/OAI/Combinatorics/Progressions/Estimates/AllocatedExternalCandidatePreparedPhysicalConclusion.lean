import OAI.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateSourcePhysicalBudgetBounds
import OAI.Combinatorics.Progressions.Dynamics.CandidateFrontActualPowerBudget
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeAdaptedConclusion
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativePhysicalConclusion
import OAI.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseCanonicalTopology

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace CommonKeepPositiveKernelPreparation

variable {P} {p : ℝ} {e : ℕ} (front : P.CommonKeepPositiveKernelPreparation p e)
    {Pivot : Type} [Fintype Pivot]
    {pFamily pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A E A.Path Pivot D Fmark φ marked
      front.keep cost pFamily pLocal pNative r periodCap coverCap Lip)
    (H : Finset A.Path) (hH : H ⊆ front.prep.selected.retained)
    (hsourceChart : F.sourceChart = front.problem.precenterChart front.prep.positive_mass)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬front.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (hscore : ∀ a ∈ H, Real.exp (-positiveKernelPreparationParameter (2 * p)) ≤
      (F.sourceCandidate a).score (fun x => (front.prep.selected.tests x).observable) weight)
    (retained : Finset A.Path) (hsub : retained ⊆ H)
    {selectedMass : ℝ} (hmass : selectedMass ≤ A.law.mass retained)

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

include hH hsourceChart in

theorem conclusion_of_actualNativeQuotient
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    {dQ : ℕ} (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup), descended x (QuotientGroup.mk
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
      (front.prep.selected.tests x).observable (QuotientGroup.mk g))
    (adapted : (RationalFilteredNilmanifold.optionProduct Q
      (fun j => (F.native j).model)).AdaptedModelData)
    {outputCost : ℝ} (hout : 0 ≤ outputCost)
    (result : (((F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen
      (fun x => (front.prep.selected.tests x).observable) weight
      (Real.exp (-positiveKernelPreparationParameter (2 * p))) hscore
      retained hsub hmass).withKeep front.keep (fun _ => rfl)).adaptedOptionQuotient
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        ideal hI Q hQ hker descended hrecovery adapted).Conclusion
          outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost)))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp outputCost)
    (hσone : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤
      Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) :
    Nonempty (P.Conclusion (3 * outputCost + 2)
      (Real.exp (-(3 * outputCost + 2))) (Real.exp (-(3 * outputCost + 2)))) := by
  have hcharts (a : A.Path) (ha : a ∈ H) :
      F.sourceChart a = front.prep.selected.problem.chart ⟨a, hH ha⟩ := by
    rw [hsourceChart]
    exact front.problem.precenterChart_mem front.prep.positive_mass a
      (front.prep.selected.subset (hH ha))
  obtain ⟨selected⟩ := F.conclusion_of_actualSourceAdaptedOptionQuotient H
    sourceCenter hpath hcenter hfrozen (fun x => (front.prep.selected.tests x).observable)
    weight (Real.exp (-positiveKernelPreparationParameter (2 * p))) hscore
    front.prep.selected.problem hH hcharts retained hsub hmass
    ideal hI Q hQ hker descended hrecovery adapted result
  exact front.conclusion_of_selected hout selected hweight hσone Cgeo hCgeo
    hchart hsmall hpoly

end CommonKeepPositiveKernelPreparation
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

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

section PrimitiveResult
variable {s : ℕ}
variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M s f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    {p : ℝ} {e : ℕ} (source : A.DegreeSourceProfile s p e)
    (data : P₀.PrimitiveFrontQuotientData FmarkNative source)

def PrimitiveFrontQuotientPhysicalTerminalAt (Cgeometry C Cbasis K T : ℕ)
    (hp : 0 ≤ p)
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ FmarkNative.filtration.layer k) : Prop :=
      let F := data.factorFamily hp
      let pFactor := source.front.factorBudget
      let pGeometry := source.front.geometryBudget
      let qVertical := 3 * source.front.familyParameter + 1
      let pGeo := (pGeometry + 2) ^ 2
      let jointGeo := (pGeometry + 3) ^ 2
      let adaptedBudget := (jointGeo + 2) ^ Cgeometry
      let bnd := adaptedBudget + (pGeo + 3) ^ 5 + pGeo + jointGeo + pGeometry + pFactor + 2
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo pFactor
      let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let stageInput := jointCost + (jointCost + K) ^ K
      let initialShortLog := max ((pFactor + 2 + C) ^ C + 7 * pFactor + 22)
        ((stageInput + 2) ^ T)
      let keepLong := fun i => data.front.keep i ∧ Real.exp initialShortLog ≤ (A.sides i : ℝ)
    ∀ [Nonempty {i // keepLong i}],
      let qCommon := (stageInput + 2) ^ T + (((stageInput + 2) ^ 2 + 2) ^ 63 + 1) + stageInput + 1
      let pProj := max qCommon 0 + adaptedBudget + 1
      let markInput := nativeOptionFixedSourceQuotientMarkInput pGeometry
      let markBudget := (markInput + 2) ^ nativeOptionFixedSourceMarkExponent.{0, 0}
      let pTerminal := (pProj + 2) ^ 4 + markInput + markBudget + jointGeo +
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
    ∀ (hFastInput : allocatedCandidateCommonFastBudget s pTerminal ≤ source.inner.x)
      (hblocks : (s : ℝ) * (markInput * m) ≤ source.inner.x)
      (hShortInput : max cost initialShortLog ≤
        (source.inner.x + source.inner.Cprimitive) ^ source.inner.Cprimitive)
      (hNativeInput : (pProj + 2) ^ 3 + qCommon ≤
        (source.inner.x + source.inner.Cprimitive) ^ source.inner.Cprimitive)
      (hMassInput : verticalDecompositionBudget qVertical *
        (Fintype.card (KernelProjectionPresentPivot data.front.prep.selected.code) : ℝ) +
        ((qCommon + 2) ^ 5 + qCommon) + source.front.familyParameter ≤ source.inner.gainLog)
      (separation : ℝ)
      (hseparation : certifiedAffineLongSideBound
        (preparedFiniteForwardCumulative source.inner.scheduleExponent
          AllocatedExternalCandidateSampler.degreeSourceCountConstants s source.inner.x) ≤ separation)
      [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
      [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
      [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
      [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)],
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))
      letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
        IsModuleTopology.isTopologicalAddGroup ℝ _
      letI := realification_moduleTopology_t2 data.quotient.basis
      ∃ desc : data.DescendedFamily,
      ∃ geometry : (optionProduct D (fun j => (F.native j).model)).AdaptedMapGeometryData
          (optionProduct data.quotient (fun j => (F.native j).model))
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (lieQuotientMap data.front.prep.nativeQuotientIdeal)) jointGeo adaptedBudget,
      ∃ markGeometry : (optionProduct data.quotient (fun j => (F.native j).model)).FixedSourceAdaptedMarkGeometryData
          (optionProduct FmarkNative (fun j => (F.native j).model)) geometry.target
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (quotientInducedMark data.front.prep.nativeQuotientIdeal φ data.ideal_killed))
          markInput markBudget,
      let hmarkΦ := D.nativeOptionFixedSourceQuotientMark_mem_layer FmarkNative
        data.front.prep.nativeQuotientIdeal data.front.prep.nativeQuotientIdeal_terminal
        data.quotient data.quotient_filtration (fun j => (F.native j).model)
        φ data.ideal_killed hφ geometry.target
      let hMark : ∀ k, (NilpotentLieFiltration.pi (optionFiltrations FmarkNative.filtration
          (fun j => (F.native j).model.filtration))).layer k =
          Submodule.span ℚ (markGeometry.target.basis '' {i | k ≤ markGeometry.target.weight i}) := by
        intro k
        exact FmarkNative.optionAdaptedModel_layers (fun j => (F.native j).model) markGeometry.target k
      F.ActualAdaptedPivotQuotientLongPhysicalTerminal keepLong data.retained P₀.centerLift
        (data.factorFamily_path_eq hp) (fun a _ => data.factorFamily_center_eq hp a)
        (fun a _ i => data.frozen_side a i)
        (fun x => (data.front.prep.selected.tests x).observable) weight
        (Real.exp (-AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)))
        (data.factorFamily_score hp) geometry.source.basis geometry.source.weight
        geometry.source.layers
        (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList
        data.quotient (data.factorFamily_quotient_filtration hp) data.ideal_killed
        (fun x => (desc.tests x).observable) desc.recovery geometry.target
        markGeometry.target.basis markGeometry.target.weight hMark hmarkΦ
        source.inner.scheduleExponent source.inner.Cprimitive source.inner.x separation qVertical qCommon pProj

end PrimitiveResult

theorem exists_primitiveFrontQuotient_actual_physical_terminal
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ Cgeometry C Cbasis K T : ℕ, 2 ≤ Cgeometry ∧ 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M s f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    {p : ℝ} {e : ℕ} (source : A.DegreeSourceProfile s p e)
    (data : P₀.PrimitiveFrontQuotientData FmarkNative source)
    (hp : 0 ≤ p)
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ FmarkNative.filtration.layer k),
      PrimitiveFrontQuotientPhysicalTerminalAt FmarkNative P₀ source data
        Cgeometry C Cbasis K T hp hφ := by
  obtain ⟨Cgeometry, C, Cbasis, K, T, hCgeometry, hC, hCbasis, hK, hT, hterminal⟩ :=
    exists_allocatedExternalCandidateSpatialNativeFamily_actual_physical_terminal s hs
  refine ⟨Cgeometry, C, Cbasis, K, T, hCgeometry, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ _ I E J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A L M _ _ _ _ d D f FmarkNative φ marked _ _ _ _ observable weight
    cost massThreshold scoreThreshold P₀ p e source data hp hφ
  dsimp only [PrimitiveFrontQuotientPhysicalTerminalAt]
  intro _ hFastInput hblocks hShortInput hNativeInput hMassInput separation hseparation _ _ _ _
  let F := data.factorFamily hp
  let pGeometry := source.front.geometryBudget
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 data.quotient.basis
  obtain ⟨desc⟩ := data.exists_descendedFamily
  have bounds := source.front.factorGeometryBudget hp
  refine ⟨desc, ?_⟩
  exact hterminal F bounds.native_vertical bounds.local_vertical bounds.vertical_factor bounds.correlation_factor
      data.retained data.mass_pos (data.factorFamily_correlation_bound hp)
      pGeometry bounds.geometry_two (data.source_geometry_bound hp) (data.mark_geometry_bound hp)
      hφ (data.mark_height_bound hp) (data.native_geometry_bound hp) (data.pivot_card_bound hp)
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList
      data.quotient (data.factorFamily_quotient_filtration hp) data.ideal_killed
      (data.quotient_geometry_bound hp) (data.quotient_projection_bound hp)
      source.inner hFastInput hblocks hShortInput hNativeInput source.front.familyParameter
      data.mass hMassInput separation hseparation
      P₀.centerLift (data.factorFamily_path_eq hp) (fun a _ => data.factorFamily_center_eq hp a)
      (fun a _ i => data.frozen_side a i)
      (fun x => (data.front.prep.selected.tests x).observable) weight
      (Real.exp (-AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)))
      (data.factorFamily_score hp) (fun x => (desc.tests x).observable) desc.recovery

end
end Erdos3.VectorPolynomial

end

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

section PrimitiveResult
variable {s : ℕ}
variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {d : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M (s + 1) f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    {p : ℝ} {e : ℕ} (source : A.DegreeSourceProfile (s + 1) p e)
    (data : P₀.PrimitiveFrontQuotientData FmarkNative source)

def PrimitiveFrontQuotientCanonicalPhysicalTerminalAt (Cgeometry C Cbasis K T : ℕ)
    (hp : 0 ≤ p)
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ FmarkNative.filtration.layer k) : Prop :=
      let F := data.factorFamily hp
      let pFactor := source.front.factorBudget
      let pGeometry := source.front.geometryBudget
      let qVertical := 3 * source.front.familyParameter + 1
      let pGeo := (pGeometry + 2) ^ 2
      let jointGeo := (pGeometry + 3) ^ 2
      let adaptedBudget := (jointGeo + 2) ^ Cgeometry
      let bnd := adaptedBudget + (pGeo + 3) ^ 5 + pGeo + jointGeo + pGeometry + pFactor + 2
      let localCost := allocatedFrozenTaggedPairBudget (s + 1) C Cbasis pGeo pFactor
      let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let stageInput := jointCost + (jointCost + K) ^ K
      let initialShortLog := max ((pFactor + 2 + C) ^ C + 7 * pFactor + 22)
        ((stageInput + 2) ^ T)
      let keepLong := fun i => data.front.keep i ∧ Real.exp initialShortLog ≤ (A.sides i : ℝ)
      let qCommon := (stageInput + 2) ^ T + (((stageInput + 2) ^ 2 + 2) ^ 63 + 1) + stageInput + 1
      let pProj := max qCommon 0 + adaptedBudget + 1
      let markInput := nativeOptionFixedSourceQuotientMarkInput pGeometry
      let markBudget := (markInput + 2) ^ nativeOptionFixedSourceMarkExponent.{0, 0}
      adaptedBudget ≤ source.inner.physicalBudget ∧
      markBudget ≤ source.inner.physicalBudget ∧
      jointGeo ≤ source.inner.physicalBudget ∧
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ source.inner.physicalBudget ∧
      (pProj + 2) ^ 4 ≤ source.inner.physicalBudget ∧
      (pProj + 2) ^ 3 + qCommon ≤ source.inner.physicalBudget ∧
      cost ≤ source.inner.physicalBudget ∧
      (∀ i, ¬keepLong i → (A.sides i : ℝ) ≤ Real.exp source.inner.physicalBudget) ∧
      Real.exp (-source.inner.physicalBudget) ≤
        Real.exp (-AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)) ∧
      Real.exp (-source.inner.physicalBudget) ≤
        Real.exp (-(verticalDecompositionBudget qVertical *
          (Fintype.card (KernelProjectionPresentPivot data.front.prep.selected.code) : ℝ) +
          ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass data.retained ∧
      pGeometry ≤ source.inner.physicalBudget ∧
      source.front.familyParameter ≤ source.inner.physicalBudget ∧
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))
      letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
        IsModuleTopology.isTopologicalAddGroup ℝ _
      letI := realification_moduleTopology_t2 data.quotient.basis
      ∃ desc : data.DescendedFamily,
      ∃ geometry : (optionProduct D (fun j => (F.native j).model)).AdaptedMapGeometryData
          (optionProduct data.quotient (fun j => (F.native j).model))
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (lieQuotientMap data.front.prep.nativeQuotientIdeal)) jointGeo adaptedBudget,
      ∃ markGeometry : (optionProduct data.quotient (fun j => (F.native j).model)).FixedSourceAdaptedMarkGeometryData
          (optionProduct FmarkNative (fun j => (F.native j).model)) geometry.target
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (quotientInducedMark data.front.prep.nativeQuotientIdeal φ data.ideal_killed))
          markInput markBudget,
      let hmarkΦ := D.nativeOptionFixedSourceQuotientMark_mem_layer FmarkNative
        data.front.prep.nativeQuotientIdeal data.front.prep.nativeQuotientIdeal_terminal
        data.quotient data.quotient_filtration (fun j => (F.native j).model)
        φ data.ideal_killed hφ geometry.target
      let hMark : ∀ k, (NilpotentLieFiltration.pi (optionFiltrations FmarkNative.filtration
          (fun j => (F.native j).model.filtration))).layer k =
          Submodule.span ℚ (markGeometry.target.basis '' {i | k ≤ markGeometry.target.weight i}) := by
        intro k
        exact FmarkNative.optionAdaptedModel_layers (fun j => (F.native j).model) markGeometry.target k
      F.ActualAdaptedPivotQuotientLongPhysicalTerminal keepLong data.retained P₀.centerLift
        (data.factorFamily_path_eq hp) (fun a _ => data.factorFamily_center_eq hp a)
        (fun a _ i => data.frozen_side a i)
        (fun x => (data.front.prep.selected.tests x).observable) weight
        (Real.exp (-AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)))
        (data.factorFamily_score hp) geometry.source.basis geometry.source.weight
        geometry.source.layers
        (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList
        data.quotient (data.factorFamily_quotient_filtration hp) data.ideal_killed
        (fun x => (desc.tests x).observable) desc.recovery geometry.target
        markGeometry.target.basis markGeometry.target.weight hMark hmarkΦ
        source.inner.scheduleExponent source.inner.Cprimitive source.inner.x source.inner.separation qVertical qCommon pProj

omit [DecidableEq X] in

theorem PrimitiveFrontQuotientPhysicalTerminalAt.toCanonical
    (Cgeometry C Cbasis K T : ℕ) (hp : 0 ≤ p)
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ FmarkNative.filtration.layer k)
    (hproduce : PrimitiveFrontQuotientPhysicalTerminalAt FmarkNative P₀ source data
      Cgeometry C Cbasis K T hp hφ)
    [Nonempty G] (hcostlt : cost < source.inner.x)
    (hgain : source.inner.x ≤ source.inner.gainLog)
    (hscale : Real.exp source.inner.x ≤ (S.value : ℝ)) :
      let pFactor := source.front.factorBudget
      let pGeometry := source.front.geometryBudget
      let qVertical := 3 * source.front.familyParameter + 1
      let pGeo := (pGeometry + 2) ^ 2
      let jointGeo := (pGeometry + 3) ^ 2
      let adaptedBudget := (jointGeo + 2) ^ Cgeometry
      let bnd := adaptedBudget + (pGeo + 3) ^ 5 + pGeo + jointGeo + pGeometry + pFactor + 2
      let localCost := allocatedFrozenTaggedPairBudget (s + 1) C Cbasis pGeo pFactor
      let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let stageInput := jointCost + (jointCost + K) ^ K
      let initialShortLog := max ((pFactor + 2 + C) ^ C + 7 * pFactor + 22)
        ((stageInput + 2) ^ T)
      let qCommon := (stageInput + 2) ^ T + (((stageInput + 2) ^ 2 + 2) ^ 63 + 1) + stageInput + 1
      let pProj := max qCommon 0 + adaptedBudget + 1
      let markInput := nativeOptionFixedSourceQuotientMarkInput pGeometry
      let markBudget := (markInput + 2) ^ nativeOptionFixedSourceMarkExponent.{0, 0}
      let pTerminal := (pProj + 2) ^ 4 + markInput + markBudget + jointGeo +
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
      allocatedCandidateCommonFastBudget (s + 1) pTerminal ≤ source.inner.x →
      ((s + 1 : ℕ) : ℝ) * (markInput * m) ≤ source.inner.x →
      max cost initialShortLog ≤ source.inner.x →
      (pProj + 2) ^ 3 + qCommon ≤ source.inner.x →
      verticalDecompositionBudget qVertical *
        (Fintype.card (KernelProjectionPresentPivot data.front.prep.selected.code) : ℝ) +
        ((qCommon + 2) ^ 5 + qCommon) + source.front.familyParameter ≤ source.inner.x →
      adaptedBudget ≤ source.inner.x → markBudget ≤ source.inner.x →
      jointGeo ≤ source.inner.x → (pProj + 2) ^ 4 ≤ source.inner.x →
      pGeometry ≤ source.inner.x → source.front.familyParameter ≤ source.inner.x →
      PrimitiveFrontQuotientCanonicalPhysicalTerminalAt FmarkNative P₀ source data
        Cgeometry C Cbasis K T hp hφ := by
  intro pFactor pGeometry qVertical pGeo jointGeo adaptedBudget bnd localCost jointCost
    stageInput initialShortLog qCommon pProj markInput markBudget pTerminal
    hfast hblocks hshort hnative hmass hadapted hmark hjoint hprojection hgeometry hfamily
  let keepLong := fun i => data.front.keep i ∧ Real.exp initialShortLog ≤ (A.sides i : ℝ)
  have hfull := source.inner.input_le_physicalBudget
  have hprimitive : source.inner.x ≤
      (source.inner.x + source.inner.Cprimitive) ^ source.inner.Cprimitive := by
    have hC : (1 : ℝ) ≤ source.inner.Cprimitive := Nat.one_le_cast.mpr source.inner.primitive_pos
    have hbase : 1 ≤ source.inner.x + source.inner.Cprimitive := by
      linarith only [source.inner.x_nonneg, hC]
    calc
      _ ≤ source.inner.x + source.inner.Cprimitive := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (source.inner.x + source.inner.Cprimitive) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hbase source.inner.primitive_pos
  have hlong : initialShortLog ≤ source.inner.x := (le_max_right _ _).trans hshort
  let : Nonempty {i // keepLong i} := data.initialLong_nonempty hcostlt hlong hscale
  change adaptedBudget ≤ source.inner.physicalBudget ∧
    markBudget ≤ source.inner.physicalBudget ∧ jointGeo ≤ source.inner.physicalBudget ∧
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ source.inner.physicalBudget ∧
    (pProj + 2) ^ 4 ≤ source.inner.physicalBudget ∧
    (pProj + 2) ^ 3 + qCommon ≤ source.inner.physicalBudget ∧
    cost ≤ source.inner.physicalBudget ∧
    (∀ i, ¬keepLong i → (A.sides i : ℝ) ≤ Real.exp source.inner.physicalBudget) ∧
    Real.exp (-source.inner.physicalBudget) ≤
      Real.exp (-AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)) ∧
    Real.exp (-source.inner.physicalBudget) ≤
      Real.exp (-(verticalDecompositionBudget qVertical *
        (Fintype.card (KernelProjectionPresentPivot data.front.prep.selected.code) : ℝ) +
        ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass data.retained ∧
    pGeometry ≤ source.inner.physicalBudget ∧
    source.front.familyParameter ≤ source.inner.physicalBudget ∧ _
  refine ⟨hadapted.trans hfull, hmark.trans hfull, hjoint.trans hfull,
    source.inner.variables_input.trans hfull, hprojection.trans hfull, hnative.trans hfull,
    hcostlt.le.trans hfull, ?_, ?_, ?_, hgeometry.trans hfull, hfamily.trans hfull, ?_⟩
  · intro i hi
    exact (data.initialLong_excluded_bound initialShortLog i hi).trans
      (Real.exp_le_exp.mpr (hshort.trans hfull))
  · exact Real.exp_le_exp.mpr (neg_le_neg
      ((source.front.familyBudget hp).projection.trans (hfamily.trans hfull)))
  · calc
      _ ≤ Real.exp (-(verticalDecompositionBudget qVertical *
          (Fintype.card (KernelProjectionPresentPivot data.front.prep.selected.code) : ℝ) +
          ((qCommon + 2) ^ 5 + qCommon))) * Real.exp (-source.front.familyParameter) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        simpa only [neg_add] using neg_le_neg (hmass.trans hfull)
      _ ≤ _ := mul_le_mul_of_nonneg_left data.mass (Real.exp_nonneg _)
  · apply OrdinaryPolynomialPhase.withCanonicalTopology
    intro _ _ _ _
    exact hproduce hfast hblocks (hshort.trans hprimitive) (hnative.trans hprimitive)
      (hmass.trans hgain) source.inner.separation source.inner.affine_floor

end PrimitiveResult

end
end Erdos3.VectorPolynomial

end

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

theorem exists_primitiveFrontQuotient_canonical_physical_terminal
    (s : ℕ) :
    ∃ Cgeometry C Cbasis K T Cfit : ℕ,
      2 ≤ Cgeometry ∧ 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧ 2 ≤ Cfit ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Nonempty G] [Fintype X] [DecidableEq X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {d : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M (s + 1) f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    {p : ℝ} {e : ℕ} (source : A.DegreeSourceProfile (s + 1) p e)
    (data : P₀.PrimitiveFrontQuotientData FmarkNative source)
    (hp : 0 ≤ p)
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ FmarkNative.filtration.layer k)
    (_hcost : cost ≤ p)
    (_hfit : (source.front.familyParameter + 2) ^ Cfit ≤ source.inner.x)
    (_hgain : source.inner.x ≤ source.inner.gainLog)
    (_hscale : Real.exp source.inner.x ≤ (S.value : ℝ)),
      PrimitiveFrontQuotientCanonicalPhysicalTerminalAt FmarkNative P₀ source data
        Cgeometry C Cbasis K T hp hφ := by
  obtain ⟨Cgeometry, C, Cbasis, K, T, hCgeometry, hC, hCbasis, hK, hT, hterminal⟩ :=
    exists_primitiveFrontQuotient_actual_physical_terminal (s + 1) (by omega)
  obtain ⟨Cfit, hCfit, hbudget⟩ := exists_candidateFrontActual_power_budget (s + 1)
    (positiveKernelNativeDescentExponent (s + 1)) Cgeometry C Cbasis K T
    nativeOptionFixedSourceMarkExponent.{0, 0}
  refine ⟨Cgeometry, C, Cbasis, K, T, Cfit, hCgeometry, hC, hCbasis, hK, hT, hCfit, ?_⟩
  intro m G X _ _ _ _ I E J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A L M _ _ _ _ d D f FmarkNative φ marked _ _ _ _ observable weight
    cost massThreshold scoreThreshold P₀ p e source data hp hφ hcost hfit hgain hscale
  have family := source.front.familyBudget hp
  have hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      source.front.familyParameter := by
    simpa only [Fintype.card_subtype_true] using family.keepCard (fun _ => True)
  obtain ⟨hcap, _, _, _, _, hnative, hmcap, hvCap, _⟩ := source.front.familyCap_bounds hp
  have hcapFamily := (candidateFrontFamilyBounds source.front.familyCap source.front.nativeBudget m
    (Fintype.card (LayerSamplerVariables G I n B)) hcap hnative hmcap hvCap).2.1
  have hlayers : (m : ℝ) ≤ source.front.familyParameter := hmcap.trans hcapFamily
  have hscl := hbudget m source.front.familyParameter family.hpFamily hlayers
    cost (Fintype.card (LayerSamplerVariables G I n B))
    (Fintype.card (KernelProjectionPresentPivot data.front.prep.selected.code))
    source.front.familyParameter (hcost.trans family.cost)
    ⟨Nat.cast_nonneg _, hvariables⟩ ⟨Nat.cast_nonneg _, data.pivot_card⟩ le_rfl
  obtain ⟨_, hfast, hshort, hnativeInput, _, _, hmass, hblocks, hfamily,
    hgeometry, hadapted, hmark, hjoint, hprojection, _⟩ := hscl
  have hcostlt : cost < source.inner.x := by
    have hbase : 1 ≤ source.front.familyParameter + 2 :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (le_add_of_nonneg_left family.hpFamily)
    have hpower : source.front.familyParameter + 2 ≤
        (source.front.familyParameter + 2) ^ Cfit := by
      calc
        _ = (source.front.familyParameter + 2) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hbase (by omega)
    exact (lt_of_le_of_lt (hcost.trans family.cost)
      (lt_add_of_pos_right _ (by norm_num : (0 : ℝ) < 2))).trans_le
      (hpower.trans hfit)
  exact PrimitiveFrontQuotientPhysicalTerminalAt.toCanonical FmarkNative P₀ source data
    Cgeometry C Cbasis K T hp hφ (hterminal FmarkNative P₀ source data hp hφ)
    hcostlt hgain hscale
    (hfast.trans hfit) (hblocks.trans hfit) (hshort.trans hfit) (hnativeInput.trans hfit)
    (hmass.trans hfit) (hadapted.trans hfit) (hmark.trans hfit) (hjoint.trans hfit)
    (hprojection.trans hfit) (hgeometry.trans hfit) (hfamily.trans hfit)

end
end Erdos3.VectorPolynomial

end

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

section PrimitiveResult
variable {s : ℕ}
variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {d : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M (s + 1) f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    {p : ℝ} {e : ℕ} (source : A.DegreeSourceProfile (s + 1) p e)
    (data : P₀.PrimitiveFrontQuotientData FmarkNative source)

theorem AllocatedExternalCandidateProblem.PrimitiveFrontQuotientData.conclusion_of_canonicalPhysicalTerminal
    {Cgeometry C Cbasis K T : ℕ}
    (hp : 0 ≤ p)
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ FmarkNative.filtration.layer k)
    (hsurj : ∀ k, ∀ y ∈ FmarkNative.filtration.layer k,
      ∃ z ∈ D.filtration.layer k, φ z = y)
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ y ∈ integerBox N, ∃ i, ∀ z,
          ‖observable y z - observable (centers i).val z‖ ≤ accuracy)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      source.inner.recursiveParameter outputCost)
    (houtput : source.inner.recursiveParameter ≤ outputCost)
    (produced : PrimitiveFrontQuotientCanonicalPhysicalTerminalAt FmarkNative P₀ source data
      Cgeometry C Cbasis K T hp hφ) :
    Nonempty (P₀.Conclusion (3 * outputCost + 2)
      (Real.exp (-(3 * outputCost + 2))) (Real.exp (-(3 * outputCost + 2)))) := by
  classical
  let F := data.factorFamily hp
  obtain ⟨hgeometry, hmark, hjoint, hvars, hproj, hnative, hcost, hshort,
    hscore, hmass, hpGeoFull, hfamilyFull, hmodels⟩ := produced
  let quotientTopology := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))
  let quotientAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let quotientSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
    inferInstance
  let quotientT2 := realification_moduleTopology_t2 data.quotient.basis
  let actualQuotientTopology : TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList)) := quotientTopology
  let actualQuotientAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList)) := quotientAdd
  let actualQuotientSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList)) := quotientSMul
  let actualQuotientT2 : T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList)) := quotientT2
  obtain ⟨desc, geometry, markGeometry, hphysical⟩ := hmodels
  let := moduleTopology ℝ (ℝ ⊗[ℚ]
    (∀ i : Option (KernelProjectionPresentPivot data.front.prep.selected.code),
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList) (fun j => (F.native j).L) i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (∀ i : Option (KernelProjectionPresentPivot data.front.prep.selected.code),
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList) (fun j => (F.native j).L) i)) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ]
    (∀ i : Option (KernelProjectionPresentPivot data.front.prep.selected.code),
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η
        (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList)
        (fun j => (F.native j).L) i)) :=
    realification_moduleTopology_t2 geometry.target.basis
  have hpFull : p ≤ source.inner.physicalBudget :=
    source.input_inner.trans source.inner.input_le_physicalBudget
  have hweightFull (x) : ‖weight x‖ ≤ Real.exp source.inner.physicalBudget :=
    (hweight x).trans (Real.exp_le_exp.mpr hpFull)
  have hnetFull : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((source.inner.physicalBudget + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ y ∈ integerBox N, ∃ i, ∀ z,
          ‖(desc.tests y).observable z - (desc.tests (centers i).val).observable z‖ ≤ accuracy := by
    apply desc.member_nets
    intro accuracy haccuracy haccuracy1
    obtain ⟨count, hcount, centers, hcenters⟩ := hnet accuracy haccuracy haccuracy1
    refine ⟨count, hcount.trans ?_, centers, hcenters⟩
    apply Real.exp_le_exp.mpr
    have hlog : 0 ≤ Real.log (1 / accuracy) :=
      Real.log_nonneg ((one_le_div haccuracy).mpr haccuracy1)
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hpFull]) e
  have hfactorGeo := source.front.factorGeometryBudget hp
  obtain ⟨retained, hsub, hmassRetained, hpos, result⟩ :=
    F.conclusion_of_actualAdaptedPivotQuotientLongPhysicalTerminal
      (scheduleExponent := source.inner.scheduleExponent) (Cprimitive := source.inner.Cprimitive)
      (x := source.inner.x)
      _ data.retained P₀.centerLift (data.factorFamily_path_eq hp)
      (fun a _ => data.factorFamily_center_eq hp a) (fun a _ i => data.frozen_side a i)
      (fun x => (data.front.prep.selected.tests x).observable) weight
      (Real.exp (-AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)))
      (data.factorFamily_score hp)
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList
      data.quotient (data.factorFamily_quotient_filtration hp) data.ideal_killed
      geometry markGeometry hφ hsurj source.inner.x_nonneg
      hgeometry hmark hjoint hvars hproj hnative hcost hshort hweightFull hscore hmass
      outputCost lowerIH houtput desc.tests desc.recovery
      (by linarith only [hfactorGeo.geometry_two]) (data.quotient_geometry_bound hp)
      desc.unit (fun x => (desc.complexity x).mono hfactorGeo.geometry_descent) hnetFull hphysical
  obtain ⟨result⟩ := result
  exact data.front.conclusion_of_actualNativeQuotient F data.retained data.retained_subset
    (data.factorFamily_sourceChart_eq hp) P₀.centerLift (data.factorFamily_path_eq hp)
    (fun a _ => data.factorFamily_center_eq hp a) (fun a _ i => data.frozen_side a i)
    (data.factorFamily_score hp) retained hsub hmassRetained
    data.front.prep.nativeQuotientIdeal data.front.prep.nativeQuotientIdeal_terminal
    data.quotient data.quotient_filtration data.ideal_killed
    (fun x => (desc.tests x).observable) desc.recovery geometry.target
    (source.inner.recursiveParameter_nonneg.trans houtput) result
    (fun x => (hweight x).trans (Real.exp_le_exp.mpr
      (source.input_inner.trans (source.inner.input_le_recursiveParameter.trans houtput))))
    F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall F.hpoly

end PrimitiveResult
end
end Erdos3.VectorPolynomial

end

end OAI

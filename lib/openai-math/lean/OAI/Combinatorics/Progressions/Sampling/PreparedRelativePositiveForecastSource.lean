import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteNestedEndpointRequirement
import OAI.Combinatorics.Progressions.Estimates.PreparedScalarNestedPowerDetection

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local instance : Nonempty A.Site := A.site_nonempty

theorem preparedRelativePositiveForecastSource
    (s Aexp Cdirect Cslice : ℕ) (constants : ℕ → ℕ)
    (Bstruct gainLog stageLog Plate : ℝ)
    (Pmaster : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s → ℝ)
    (hdirect : ∀ k : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s,
      A.NativeDetection (preparedFiniteNestedForwardAllDegreeDegree k)
        ((preparedFiniteForwardParameter Aexp constants
          (preparedFiniteNestedForwardAllDegreeStage k).val
          (preparedFiniteNestedForwardAllDegreeSeed Aexp constants Bstruct k) + Cslice) ^ Cslice)
        ((preparedFiniteForwardDetectorPolynomial s).eval₂ (Nat.castRingHom ℝ)
          (allocatedModelTestLog
            (preparedFiniteForwardPairedSourcePrecision Aexp Cdirect constants
              (preparedFiniteNestedForwardAllDegreeStage k).val
              (preparedFiniteNestedForwardAllDegreeIsDirect k)
              (preparedFiniteNestedForwardAllDegreeSeed Aexp constants Bstruct k) gainLog stageLog)
            (preparedFiniteForwardWork Aexp constants
              (preparedFiniteNestedForwardAllDegreeStage k).val
              (preparedFiniteNestedForwardAllDegreeSeed Aexp constants Bstruct k))))
        (preparedModularGeneralDetectorResources
          (preparedModularGeneralDetectorConstants m (preparedFiniteNestedForwardAllDegreeDegree k))
          (preparedFiniteNestedForwardAllDegreeDegree k + 1) (Pmaster k) Plate).nativeBudget
        (preparedFiniteNestedForwardFixedCenterThreshold Aexp constants Bstruct gainLog stageLog k))
    (hAexp : 2 ≤ Aexp) (hB : 0 ≤ Bstruct)
    (hgain : gainLog ∈ Set.Icc 0 Bstruct) (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hξsource hξtarget : ξ ≤ 1)
    (hmarginSource hmarginTarget : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    (knob rawCap capLog : ℝ) :
    let seed := candidateNestedForwardSeed Aexp constants (s + 1) (2 * s + 2) Bstruct
    let u := preparedFiniteForwardModelPrecision Aexp constants (s + 1) seed gainLog stageLog
    let p := preparedFiniteForwardWork Aexp constants (s + 1) seed
    let sliceLog := (preparedFiniteForwardParameter Aexp constants (s + 1) seed + Cslice) ^ Cslice
    let testLog := (preparedFiniteForwardDetectorPolynomial s).eval₂ (Nat.castRingHom ℝ)
      (allocatedModelTestLog
        (preparedFiniteForwardSourcePrecision Aexp constants (s + 1) seed gainLog stageLog) p)
    let native := (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m 0) 1
      (Pmaster (preparedFiniteNestedForwardAllDegreeAnchor (2 * s + 2) (s + 1) s)) 0).nativeBudget
    let Econditional := preparedNestedFrontProjectionEnvelope Aexp constants (s + 1)
      (fun k : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s => k.1.val)
      (fun k : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s => k.2.1.val)
      (fun k : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s =>
        (preparedModularGeneralDetectorResources
          (preparedModularGeneralDetectorConstants m (preparedFiniteNestedForwardAllDegreeDegree k))
          (preparedFiniteNestedForwardAllDegreeDegree k + 1) (Pmaster k) Plate).nativeBudget)
      Bstruct gainLog stageLog knob
    sliceLog * Fintype.card (LayerSamplerVariables G I n B) ≤ p →
    rawCap ≤ Real.exp p → capLog ≤ p →
    (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξsource hmarginSource)) rawCap ≤
        6 * positiveProjectionAccuracy Econditional →
    1 ≤ max 1 rawCap ∧ max 1 rawCap ≤ Real.exp p ∧
      A.NativeDetection 0 sliceLog testLog native
        (forecastAugmentedUnitThreshold u p
          (Real.exp (sliceLog * Fintype.card (LayerSamplerVariables G I n B)))
          (max 1 rawCap) (Real.exp capLog)) ∧
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
        (A.law.siteLaw (A.physicalBox hξtarget hmarginTarget)) (max 1 rawCap) ≤
          6 * positiveProjectionAccuracy knob := by
  intro seed u p sliceLog testLog native Econditional hSliceLog hRawCap hCap hexcess
  have hseed0 : 0 ≤ seed :=
    candidateNestedForwardSeed_nonneg Aexp constants (s + 1) (2 * s + 2) hB
  have hseed : Bstruct ≤ seed :=
    le_candidateNestedForwardSeed Aexp constants (s + 1) (2 * s + 2) hAexp hB
  have hu : 0 ≤ u := (preparedFiniteForward_model_precision_bounds Aexp constants (s + 1)
    hseed0 ⟨hgain.1, hgain.2.trans hseed⟩ ⟨hstage.1, hstage.2.trans hseed⟩).1
  have hp : 0 ≤ p := preparedFiniteForwardWork_nonneg Aexp constants (s + 1) hseed0
  have hPrecision : knob ≤ Econditional :=
    preparedNestedFrontProjectionEnvelope_endpoint_le Aexp constants (s + 1)
      _ _ _ knob hAexp hB hgain hstage
  have hterminal := preparedRelativePositiveTerminalDetection A s Aexp Cdirect Cslice constants
    Bstruct gainLog stageLog Plate Pmaster hdirect
  have hnative := preparedModularGeneralDetectorResources_nativeBudget_eq
    (preparedModularGeneralDetectorConstants m 0) 1
    (Pmaster (preparedFiniteNestedForwardAllDegreeAnchor (2 * s + 2) (s + 1) s)) Plate (0 : ℝ)
  dsimp only at hterminal
  rw [hnative] at hterminal
  exact A.fixedCenter_forecast_source_bounds hξsource hξtarget hmarginSource hmarginTarget
    A.integerBox_nonempty hu hp hSliceLog hRawCap hCap hPrecision hterminal hexcess

end Erdos3.VectorPolynomial

end

end OAI

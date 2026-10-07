import OAI.Combinatorics.Progressions.Estimates.AllocatedZeroLayerFixedCenterExcess
import OAI.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeDirectMasterBudget
import OAI.Combinatorics.Progressions.Probability.PreparedFullChartConditionalNativeDetectionSharedWidth

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section General

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (sourceU pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

def PreparedScheduledDirectSourceAvailability
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ) : Prop :=
  ∀ α : ℝ, Real.exp (-(2 * sourceU + 4 * pModel + 7)) ≤ α → α ≤ 1 →
    PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := sourceU) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

include ν bW μ in

theorem preparedFiniteScheduleGeometryDirectSource
    (Cdetect : ℕ) (hCdetect : Cdetect = sampledSupportedSlicedDetectionConstant s Pdetect)
    (hsm : s ≤ m)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog sourceU pModel) pRadius
      (2 * sourceU + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσone : ∀ j, σ j ≤ 1)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hcapacity : (s + 1) * (s + 3) ≤ Fintype.card G) :
    PreparedScheduledDirectSourceAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  let : CompactSpace (CoefficientTorus (K := Fin (s + 1)) U) :=
    coefficientTorus_compact_of_lattice U
  let : MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U) := borel _
  let : BorelSpace (CoefficientTorus (K := Fin (s + 1)) U) := ⟨rfl⟩
  let : MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U) := borel _
  let : BorelSpace (SiteTorus (Finset (Fin (s + 1))) U) := ⟨rfl⟩
  intro α hαlower hαone
  rw [hCdetect] at scalar geometryAt
  exact preparedUniformDegreeDirectSource_of_geometry
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := sourceU) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (α := α) (τ := τ)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ)
    (μrows := probabilityAddHaar (CoefficientTorus (K := Fin (s + 1)) U))
    hsm Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius
    scalar geometryAt hRone hRinv hσone hSLate hBa hBi hcapacity hαlower hαone

end General

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

private def AllocatedNativeSliceDetection
    {m degree : ℕ} {X K Ω : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K] [Fintype Ω]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sides : K → ℕ) (law : FiniteProbabilityWeights Ω)
    (physical : Ω → integerBox sides → X → ℤ) (pSlice pTest pNative α : ℝ) : Prop :=
  ∀ {Tests : Ω → Type} [∀ z, Nonempty (Tests z)]
    {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)]
    [∀ z j, LieAlgebra ℚ (Ldetect z j)] {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
    (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) degree (dims z j))
    (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : K => 1))
    (slices : ∀ z, Tests z → Finset (integerBox sides))
    (origin : ∀ z, Tests z → K → ℤ) (step : ∀ z, Tests z → ℕ)
    (length : ∀ z, Tests z → K → ℕ),
    (∀ z j, 0 < step z j) →
    (∀ z j, (slices z j).image Subtype.val = commonStrideBox (origin z j) (step z j) (length z j)) →
    (∀ z j, IsDenseCommonStrideBox sides pSlice ((slices z j).image Subtype.val)) →
    (∀ z j, (Vdetect z j).ComplexityLE pTest) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    SampledSliceNativeDetection J N hbox poly law physical slices
      (fun z j t => star ((Vdetect z j).eval (commonStrideIndex (origin z j) (step z j) t.val)))
      degree pNative α

variable {m s nX : ℕ} {G : Type} [Fintype G] [decG : DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)
    (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
    (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
    (α τ : ℝ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

local notation "pTest" => Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog u pModel)

theorem exists_allocatedExternalCandidateSamplerFamily_nativeDetection
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hPrepared : PreparedModularGeneralConditionalDetectionFreeTrimSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    (hτ : 0 < τ) (hτInv : τ⁻¹ ≤ Real.exp Pphysical)
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog u pModel) (allocatedModelTestLog u pModel) (α / 2))
      Pphysical coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s)
        (s + 1) Pmaster Plate).required ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s)
        (s + 1) Pmaster Plate).required ≤ Rrank)
    (hCells : cells.Nonempty) (hα : 0 < α)
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pTest) :
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s)
      (s + 1) Pmaster Plate
    ∃ A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hmem τ ξ stride cells,
      (∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
        let Zc := selectedJointDensityMass
          (trimmedIntegerBox N (spatialTrimMargin τ N)) stride cells
          (allocatedExternalCandidateWidths B U basis S N τ ξ)
          (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
        |Zc - 1| ≤ Real.exp (-r.E) ∧ Zc ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
          0 < Zc ∧ Zc⁻¹ ≤ 2) ∧
      ∀ center, (A center).NativeDetection s pSlice pTest r.nativeBudget α := by
  intro r
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hcenter, hweight, hdetect⟩ :=
    hPrepared hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff hτ hτInv hτHalf hτDim hξ hξSmall hξLate
      cells poly hp hmem hsize hrank hRank hCells
  have hV := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hτ hξ N hN
  have hD : ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
      AllocatedNativeSliceDetection (degree := s) J N hbox poly
        (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S))
        (selectedJointFiniteLaw (trimmedIntegerBox N (spatialTrimMargin τ N)) hbases stride cells
          (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
            (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ N)
          hV hmass
          (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
          (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem center)
          (hcenter center).2.2.1)
        (fun z t => jointIntegerPhysicalSite t.val (z.1.val, z.2.val))
        pSlice pTest r.nativeBudget α := by
    intro center Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices origin step length
      hstep hshape hdense hcomplex hnorm signal hsignal hsupp hlarge
    exact hdetect center Ddetect Vdetect slices origin step length hstep hshape hdense
      hdimension hcomplex hnorm signal hα hsignal hsupp hlarge
  clear hdetect hweight hnormalizer
  have hwidth : allocatedExternalCandidateWidths B U basis S N τ ξ =
      narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ N := by
    exact allocatedExternalCandidateWidths_eq B U basis S N τ ξ
  have hdec : (fun a b : Fin nX => Classical.propDecidable (a = b)) =
      instDecidableEqFin nX := Subsingleton.elim _ _
  have hdecG : (fun a b : G => Classical.propDecidable (a = b)) = decG :=
    Subsingleton.elim _ _
  revert hV hbases hbox hmass hcenter hD
  rw [← hdec, ← hdecG, ← hwidth]
  intro hbases hbox hmass hcenter hV hD
  let A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hmem τ ξ stride cells :=
    fun center => ⟨hN, hτ, hξ, hstride, hbases, hmass, (hcenter center).2.2.1⟩
  refine ⟨A, hcenter, ?_⟩
  exact hD

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ} (selection : Fin (s + 1) ↪ G) (Pdetect : Polynomial ℕ)

theorem preparedFiniteScheduleDirectWidth_inv
    (Cdetect : ℕ)
    (hCdetect : Cdetect = sampledSupportedSlicedDetectionConstant s Pdetect)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice α : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog sourceU pModel) pRadius
      (2 * sourceU + 4 * pModel + 7) pGain)
    (hα : Real.exp (-(2 * sourceU + 4 * pModel + 7)) ≤ α) :
    (normalizedTupleNarrowWidth (Fin nX) (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog sourceU pModel) (allocatedModelTestLog sourceU pModel) α)
      Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate := by
  rw [hCdetect] at scalar geometryAt
  have hMk := (geometryAt.2 α hα).2.1
  have hCoarse : 0 ≤ coarseTarget := by
    linarith only [scalar.gain_master.1, scalar.coarse_lower]
  have hwidth := preparedModularDetector_narrow_width B selection scalar.physical_master.1
    hCoarse (hMk.trans (Real.exp_le_exp.mpr scalar.kernel_physical))
    scalar.detector_physical scalar.variables_physical scalar.ambient_physical
  exact hwidth.2.trans (Real.exp_le_exp.mpr scalar.xi_late)

theorem preparedFiniteScheduleDirectWidth
    (Cdetect : ℕ)
    (hCdetect : Cdetect = sampledSupportedSlicedDetectionConstant s Pdetect)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice α : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog sourceU pModel) pRadius
      (2 * sourceU + 4 * pModel + 7) pGain)
    (hα : Real.exp (-(2 * sourceU + 4 * pModel + 7)) ≤ α) :
    Real.exp (-Plate) ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog sourceU pModel) (allocatedModelTestLog sourceU pModel) α)
      Pphysical coarseTarget := by
  have h := preparedFiniteScheduleDirectWidth_inv B U basis S selection Pdetect Cdetect
    hCdetect Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical
    coarseTarget pRadius sourceU pModel pSlice α scalar geometryAt hα
  have hchoice := sharedWidthNormalizedTuplePreparedChoice (fun _ : Unit => s + 1)
    (fun _ => allocatedDetectedKernelCutoff s G
      (Fintype.card (LayerSamplerVariables G I n B)) Pdetect
      (allocatedModelTestLog sourceU pModel) (allocatedModelTestLog sourceU pModel) α)
    (fun _ => selection) (fun _ => Pphysical) (fun _ => coarseTarget) Plate (fun _ => h)
  exact hchoice.2.2 ()

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {Stage : Type} (degree : Stage → ℕ)
variable (selection : ∀ k, Fin (degree k + 1) ↪ G)
variable (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable (sourceU modelLog sliceLog α : Stage → ℝ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem preparedFiniteScheduleCandidateDetection
    (Pchart Qstride Pmaster Plate Pphysical coarseTarget : ℝ) (pGain : Stage → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDirectSourceAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate (pGain k) Pphysical coarseTarget)
    (hαLower : ∀ k, Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2)
    (hαHalfOne : ∀ k, α k / 2 ≤ 1)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    (hτ : 0 < τ) (hτInv : τ⁻¹ ≤ Real.exp Pphysical)
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ∀ k, ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) (selection k)
      (allocatedDetectedKernelCutoff (degree k) G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog (sourceU k) (modelLog k))
        (allocatedModelTestLog (sourceU k) (modelLog k)) (α k / 2))
      Pphysical coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ k i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) Pmaster Plate).required ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : ∀ k, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) Pmaster Plate).required ≤ Rrank)
    (hCells : cells.Nonempty)
    (hdimension : ∀ k, (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
    (A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hmem τ ξ stride cells) :
    ∀ k center, (A center).NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) Pmaster Plate).nativeBudget (α k) := by
  intro k
  have hDirect := hAvailable k (α k / 2) (hαLower k) (hαHalfOne k)
  have hconditional := preparedModularGeneralConditionalDetectionFreeTrimSharedWidth_of_direct
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection k) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
    (Vtail := Vtail) (α := α k) (τ := τ) (hb := hb) (o := o)
    Pchart Qstride Pmaster Plate (pGain k) Pphysical coarseTarget hDirect
  have hα : 0 < α k := by
    have hhalf := (Real.exp_pos _).trans_le (hαLower k)
    linarith only [hhalf]
  obtain ⟨Ak, _hcenter, hdetect⟩ :=
    exists_allocatedExternalCandidateSamplerFamily_nativeDetection
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := Vtail) (α := α k) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate (pGain k) Pphysical coarseTarget hconditional
      hstride hstrideBound C hC hCbound hchart Cforward hforward hForward hVtail hVactual
      hprofile hcutoff hτ hτInv hτHalf hτDim hξ (hξSmall k) hξLate
      cells poly hp hmem (hsize k) hrank (hRank k) hCells hα (hdimension k)
  have hsame : Ak = A := Subsingleton.elim _ _
  rw [hsame] at hdetect
  exact hdetect

end Erdos3.VectorPolynomial

end

end OAI

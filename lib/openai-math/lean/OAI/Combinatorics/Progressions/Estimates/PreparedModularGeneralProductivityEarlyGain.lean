import OAI.Combinatorics.Progressions.Dynamics.DetectedCanonicalPhysicalBudget
import OAI.Combinatorics.Progressions.Estimates.PreparedDetectedCanonicalNativeSource
import OAI.Combinatorics.Progressions.Geometry.SharedWidthAllocatedDetectedSpatialNativeSourceGeneral

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem preparedModularCanonicalDetector_early_dimensions
    (Jalloc A : ℕ) {M : ℕ} (hM : ∀ j, Fintype.card (L j).Coord ≤ M)
    {P : ℝ} (hP : 0 ≤ P)
    (hnum : (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ P) :
    let Pearly := P + (2 * P + A) ^ A + 2
    let count := Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
      (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
      (EnlargedPreparedCommonSamplerBlock L Jalloc))
    0 ≤ Pearly ∧ P ≤ Pearly ∧ (m : ℝ) ≤ Pearly ∧ (count : ℝ) ≤ Pearly ∧
      (∀ j, (Fintype.card (PreparedSamplerContinuous L j) : ℝ) ≤ Pearly) ∧
      (∀ j, (preparedSamplerTransverse L j : ℝ) ≤ Pearly) := by
  intro Pearly count
  have hPP : P ≤ Pearly := by
    have hpow : 0 ≤ (2 * P + A) ^ A := by positivity
    dsimp only [Pearly]
    linarith
  have hm : m ≤ enlargedPreparedCommonSamplerDimension m M Jalloc := by
    unfold enlargedPreparedCommonSamplerDimension
    omega
  obtain ⟨hcount, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hM
  exact ⟨hP.trans hPP, hPP, (Nat.cast_le.mpr hm).trans (hnum.trans hPP),
    (Nat.cast_le.mpr hcount).trans (hnum.trans hPP),
    fun j => (Nat.cast_le.mpr (hI j)).trans (hnum.trans hPP),
    fun j => (Nat.cast_le.mpr (hn j)).trans (hnum.trans hPP)⟩

theorem preparedModularCanonicalDetector_early_cap
    (Jalloc A : ℕ) {M : ℕ} (hM : ∀ j, Fintype.card (L j).Coord ≤ M)
    {P pRadius pSlice u : ℝ} (hP : 0 ≤ P)
    (hnum : (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ P)
    (hpSlice : 0 ≤ pSlice) (hu : 0 ≤ u)
    (R : Fin m → ℝ) (Vtail : Fin m → ℝ≥0)
    (hR : ∀ j, 0 < R j) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hRadius : pRadius ≤ P + (2 * P + A) ^ A + 2)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    let G := EnlargedPreparedCommonKernel m Jalloc
    let I := PreparedSamplerContinuous L
    let n := preparedSamplerTransverse L
    let B := EnlargedPreparedCommonSamplerBlock L Jalloc
    let count := Fintype.card (LayerSamplerVariables G I n B)
    let Pearly := P + (2 * P + A) ^ A + 2
    let pModel := allocatedEarlyModelLog Pearly pSlice count
    let Ctail := 4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j)
    let Kslice := Real.exp (pSlice * count)
    let pDetect := allocatedModelTestLog u pModel
    let α := allocatedModelUnitThreshold u pModel Kslice Ctail
    let aDetect := 2 * u + 4 * pModel + 7
    0 ≤ pModel ∧ pSlice ≤ pModel ∧ Pearly ≤ pModel ∧ pSlice * count ≤ pModel ∧
      0 ≤ Ctail ∧ Ctail ≤ Real.exp pModel ∧ Kslice ≤ Real.exp pModel ∧
      (count : ℝ) ≤ Real.exp pModel ∧
      0 ≤ pDetect ∧ pSlice ≤ pDetect ∧
      0 < α ∧ α ≤ 1 ∧ 0 ≤ aDetect ∧ Real.exp (-aDetect) ≤ α ∧
      count * Real.exp (-pDetect) ≤ α / 8 ∧ Real.exp (-pDetect) ≤ α / 4 := by
  intro G I n B count Pearly pModel Ctail Kslice pDetect α aDetect
  obtain ⟨hearly, hPP, hm, hcount, hI, hn⟩ :=
    preparedModularCanonicalDetector_early_dimensions L Jalloc A hM hP hnum
  have h := allocatedEarlyDetector_parameters (fun j => Fintype.card (I j)) n R
    (fun j => (Vtail j : ℝ)) count hearly hpSlice hu hm hcount hR
    (fun j => (Vtail j).coe_nonneg) hI hn
    (hprofile.trans (Real.exp_le_exp.mpr hPP))
    (fun j => (hRinv j).trans (Real.exp_le_exp.mpr hRadius))
    (fun j => (hVtail j).trans (Real.exp_le_exp.mpr hPP))
  have hcap0 := earlyFiberCapLog_nonneg hearly
  have hcnt0 : (0 : ℝ) ≤ count := Nat.cast_nonneg _
  have hproduct := mul_nonneg hpSlice hcnt0
  have hpSliceModel : pSlice ≤ pModel := by
    dsimp only [pModel, allocatedEarlyModelLog]
    nlinarith
  have hPModel : Pearly ≤ pModel := by
    dsimp only [pModel, allocatedEarlyModelLog]
    nlinarith
  exact ⟨h.1, hpSliceModel, hPModel, h.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (pDetect qDetect α : ℝ)
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (s + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

structure AllocatedEarlyNativeSourceGeometryGeneral
    (Pchart P D target Pk Prho Qstride pDetect : ℝ) (K : ℝ≥0) where
  hP : 0 ≤ P
  hRP : ∀ j, R j ≤ Real.exp P
  hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P
  hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P
  hcount : ∀ j : Fin m, (Fintype.card
    (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P
  hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D
  hPk : 0 ≤ Pk
  hPrho : 0 ≤ Prho
  htarget : 0 ≤ target
  hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target (pDetect + 1)
    (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value
  η : ℝ
  hη0 : 0 ≤ η
  hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4))
  ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0
  t : ℝ
  htone : t ≤ 1
  hs : AllocatedAffineCoveredComparison.{0, 0, _, _, _, _, _} (G := G) B rows
    (Real.exp (-(pDetect + 1))) η ρ t htone
  hρ : ∀ partition, 0 < ρ partition
  hρ1 : ∀ partition, ρ partition ≤ 1
  hρlog : ∀ partition, (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho
  hσsmall : ∀ j, σ j ≤ t
  T : Fin m → ℝ
  hT : ∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j
  hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
        ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j
  siteRadius : ℝ≥0
  hrone : 1 ≤ siteRadius
  hradius : ∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)
  hbudgets : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp Pchart) →
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
    (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
    (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)
  hK : ∀ j, (R j)⁻¹ ≤ K

def AllocatedPreparedNativeInterfaceGeneral
    (Pchart P _D target Pk Prho Qstride : ℝ) (K : ℝ≥0) : Prop :=
    ∀ (_hMkP : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp P)
    (_hMkPk : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pk)
    (_hQstride : 0 ≤ Qstride)
    (_hstride : ∀ i, 0 < stride i)
    (_hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ)
    (_hC : ∀ j, 0 ≤ C j)
    (_hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (_hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    {Pbox Vlog Nlog Mlog baseAmbient : ℝ}
    (_hPbox : 0 ≤ Pbox)
    (_hVlog : 0 ≤ Vlog)
    (_hNlog : 0 ≤ Nlog)
    (_hMlog : 0 ≤ Mlog)
    (_hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (_hvolume : allocatedFullGridNaturalVolume B U basis S rowSets ≤ Real.exp Vlog)
    (_hnormalizer : ‖((allocatedProductIdealNormalizer B U basis S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp Nlog)
    (_hmaskLog : (Fintype.card (LayerSamplerAxis I n) : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * (((m + 1 : ℕ) : ℝ) * Pk)) ≤ Mlog)
    (_hbaseAmbient : 0 ≤ baseAmbient)
    (_hvbase : Vlog ≤ baseAmbient)
    (_hnbase : Nlog ≤ baseAmbient)
    (_hmbase : Mlog ≤ baseAmbient)
    (_hsites : (Fintype.card (Finset (Fin (s + 1))) : ℝ) ≤ baseAmbient)
    (_haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ baseAmbient)
    (_hlabelLog : (∑ j, (n j : ℝ) * (((m + 1 : ℕ) : ℝ) * Pk)) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (((m + 1 : ℕ) : ℝ) * Pk) ≤ baseAmbient)
    (_hKbase : (K : ℝ) ≤ Real.exp baseAmbient)
    (_hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (_hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp baseAmbient)
    (_hperiodLog : ((m + 1 : ℕ) : ℝ) * Pk ≤ baseAmbient)
    (_hrowsAmbient : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (_houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ baseAmbient)
    (_hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp baseAmbient)
    (Qgrid : ℝ≥0)
    (_hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U basis S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U basis S a).1 (allocatedGridIntegerAxis B U basis S a).2) : ℝ) + 1) ≤ Qgrid)
    (Ag : ℝ≥0)
    (_hAg : LipschitzWith Ag Real.smoothTransition)
    (_hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (_hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg : ℝ}
    (_hDg : 0 ≤ Dg)
    (_hvg : 0 ≤ vg)
    (_hwg : 0 ≤ wg)
    (_hcube : (Fintype.card (Fin (s + 1)) : ℝ) ≤ Dg)
    (_hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (_hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card : ℝ) ≤ Dg)
    (_htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (_hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (_hRv : ∀ j, R j ≤ Real.exp vg)
    (_hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (_hδw : pDetect + 1 ≤ wg)
    (_hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (_haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ Dg)
    (_hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Dg)
    (_hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ Dg)
    (_hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ Dg)
    (_hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ Dg)
    {Banalytic : ℝ}
    (_hBanalytic : 0 ≤ Banalytic)
    (_hDanalytic : Dg ≤ Banalytic)
    (_hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Banalytic)
    (_hcoordAnalytic : ((K * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Banalytic)
    (_hgridAnalytic : (Qgrid : ℝ) ≤ Real.exp Banalytic)
    {Pnum : ℝ}
    (_hPnum : 0 ≤ Pnum)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum)
    (_hn : ∀ j, (n j : ℝ) ≤ Pnum)
    (_hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
    (_hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
    (_hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Real.exp Pnum)
    {Pproj coarseTarget Ecoarse pGain : ℝ},
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin (s + 1)))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    ∀ {τ Pphysical : ℝ},
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    let ξn := normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) Pphysical coarseTarget
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (signal : ((Fin nX) → ℤ) → ℂ),
    (∀ u ∈ integerBox N, ‖signal u‖ ≤ 1) →
    (∀ u, u ∉ integerBox N → signal u = 0) →
    ∀ {lossTarget Psample Rrank Sstride εsample ηsample : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → (hτSpatial : 0 < τ) →
    0 ≤ Psample → (Fintype.card (Fin nX) : ℝ) ≤ Psample →
    (Fintype.card (Option (Fin (s + 1)) × (Fin nX)) : ℝ) ≤ Psample →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{0,0,0} m (s + 1))
    (∀ i, Real.exp ((Psample + A) ^ A) ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Psample →
    ambientBudget ≤ Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    (_hPhysicalNonneg : 0 ≤ Pphysical) → (_hMkPhysicalBound : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pphysical) →
    (_hmPhysicalBound : ((m + 1 : ℕ) : ℝ) ≤ Pphysical) → (_hCoarseNonneg : 0 ≤ coarseTarget) →
    (_hDimPhysicalBound : (((s + 1) + 1 : ℕ) : ℝ) ≤ Pphysical) →
    (_hGPhysicalBound : (Fintype.card G : ℝ) ≤ Pphysical) →
    (_hXPhysicalBound : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical) →
    lossTarget + coefficientErrorSpatialLog Pphysical + 8 ≤ target →
    ηsample ≤ Real.exp (-target) → εsample ≤ Real.exp (-target) →
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m (s + 1))
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m (s + 1))
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin (s + 1))) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * ((m + 1 : ℕ) * Pk))
    let Cgrid := Classical.choose (exists_preparedModularCanonicalDetector_grid_parameters.{0} m (s + 1) Ag)
    let Qlog := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
    let tg := ((s + 1 : ℕ) : ℝ) + Qlog + (pDetect + 1) + 1
    let pg := (Cgrid : ℝ) + (((s + 1) + 1 : ℕ) : ℝ) * Qlog + (pDetect + 1) + 4
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
    Dg ∈ Set.Icc 0 Pnative → p ∈ Set.Icc 0 Pnative → vg ∈ Set.Icc 0 Pnative →
    Fmodel ∈ Set.Icc 0 Pnative → Prho ∈ Set.Icc 0 Pnative → Pk ∈ Set.Icc 0 Pnative →
    target ∈ Set.Icc 0 Pnative → Banalytic ∈ Set.Icc 0 Pnative →
    Pphysical ∈ Set.Icc 0 Pnative → Ecoarse ∈ Set.Icc 0 Pnative → pGain ∈ Set.Icc 0 Pnative →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pphysical) →
    1 / τ ≤ Real.exp Pphysical →
    Real.exp (-pGain) / 2 ≤ (allocatedDetectedGain s (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) / 2 →
    pGain + 32 ≤ Pproj → pGain + 32 ≤ coarseTarget →
    pGain + 32 ≤ Ecoarse → pGain + 32 ≤ lossTarget →
    ∀ (Cproj Vproj : Fin m → ℝ≥0),
    let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (s + 1))
    let coverLog := (Pproj + ((s + 1) + 2 : ℕ) + Acover) ^ Acover
    let Asample := Classical.choose (exists_allocatedCanonicalProjection_composed_budget m (s + 1) Acover)
    let Pmass := (Pproj + Asample) ^ Asample
    coverLog ≤ baseAmbient → coverLog ≤ Psample → Pmass ≤ Psample →
    (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ Cproj j * ‖z‖) →
    (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vproj j) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pmass →
    (Fintype.card (Option (Fin (s + 1)) × Fin nX) : ℝ) ≤ Pmass →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pmass) → 1 / τ ≤ Real.exp Pmass →
    let AmassWindow := Classical.choose (exists_translated_physical_jet_density_window_mass.{0,0,0,max 0 0 0} m (s + 1))
    (∀ i, Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ (N i : ℝ)) →
    Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ Rrank →
    (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Pmass →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Pmass →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Pphysical →
    1 ≤ Pproj → (m : ℝ) ≤ Pproj →
    (Fintype.card G : ℝ) ≤ Pproj → (S.value : ℝ) ≤ Real.exp Pproj →
    ((m + 1 : ℕ) : ℝ) * Pk ≤ Pproj →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pproj → W ≤ Real.exp Pproj →
    (∀ j, (R j)⁻¹ ≤ Real.exp Pproj) → (∀ j, (σ j)⁻¹ ≤ Real.exp Pproj) →
    (∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pproj) →
    (∀ j, (Fintype.card (I j) : ℝ) ≤ Pproj) → (∀ j, (n j : ℝ) ≤ Pproj) →
    (∀ j, (Fintype.card (J j) : ℝ) ≤ Pproj) →
    (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pproj →
    (∀ j, (Cproj j : ℝ) ≤ Real.exp Pproj) → (∀ j, (Vproj j : ℝ) ≤ Real.exp Pproj) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pproj →
    (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ Pproj →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pproj) → τ⁻¹ ≤ Real.exp Pproj → ξn⁻¹ ≤ Real.exp Pproj →
    let Aproj := Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (s + 1)))
    (∀ i, Real.exp ((Pproj + Aproj) ^ Aproj) ≤ (N i : ℝ)) →
    Real.exp ((Pproj + Aproj) ^ Aproj) ≤ Rrank →
    ∀ {Pside : ℝ}, Pproj ≤ Pside → Pmass ≤ Pside →
    Pphysical ≤ Pside → coarseTarget ≤ Pside →
    (∀ i, Real.exp ((Pside + Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{0,0,0,0} m)) ^
      Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{0,0,0,0} m)) ≤ (N i : ℝ)) →
    cells.Nonempty → ∀ (bases : Finset (Fin nX → ℤ)), (hbases : bases.Nonempty) →
    let hξn := normalizedTupleNarrowWidth_pos (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) Pphysical coarseTarget
    ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z),
    (htotal : 0 < selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)) →
    let Path := bases × rectangularWeightIndices 0 V 1
    let pathLaw := allocatedOriginalPathLaw B U basis hb o hR hσ S (Fin nX) poly hmem N
      (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hW hτSpatial hξn stride cells hmass bases hbases htotal
    ∀ {Tdetect : Type} [Fintype Tdetect] [Nonempty Tdetect]
      (e : Tdetect → LayerSamplerVariables G I n B → ℤ), Function.Injective e →
    ∀ {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
      {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)] [∀ z j, LieAlgebra ℚ (Ldetect z j)]
      {dims : ∀ z, Tests z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) s (dims z j))
      (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
      (slices : ∀ z, Tests z → Finset Tdetect)
      (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
      (stepdetect : ∀ z, Tests z → ℕ)
      (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < stepdetect z j) →
    (∀ z j, (slices z j).image e = commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j)) →
    0 ≤ pDetect → 0 ≤ qDetect →
    (∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)) pDetect ((slices z j).image e)) →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect →
    (∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect)) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    0 < α → α ≤ 1 →
    Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-pDetect) ≤ α / 8 →
    Real.exp (-qDetect) ≤ α / 4 →
    α ≤ sampledSliceSeminorm pathLaw
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((Vdetect z j).eval (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal →
    (s + 1) * (s + 3) ≤ Fintype.card G → (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) ≤ S.value →
    let C := Classical.choose (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)
    let Bbudget := (Pnative + C) ^ C
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{0,0,0,0,0,0} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun u : integerBox N => u.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => signal u.val) (fun u => star (twistData.eval N poly u.val) * Fnative u)‖

include hb o bW μ ν μrows hR hσ in

theorem allocatedPreparedNativeInterfaceGeneral_of_geometry
    (hsm : s ≤ m)
    (Pchart D target Pk Prho Qstride : ℝ) (K : ℝ≥0)
    (geometry : AllocatedEarlyNativeSourceGeometryGeneral (s := s) (B := B) (U := U) (basis := basis)
      (S := S) (nX := nX) Pchart P D target Pk Prho Qstride pDetect K) :
    AllocatedPreparedNativeInterfaceGeneral (B := B) (U := U) (basis := basis)
      (hR := hR) (hσ := hσ) (S := S) (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (pDetect := pDetect) (qDetect := qDetect) (α := α)
      (Q := Q) (hb := hb) (o := o) Pchart P D target Pk Prho Qstride K := by
  unfold AllocatedPreparedNativeInterfaceGeneral
  intro hMkP hMkPk hQstride hstride hstrideBound C hC hCbound hchart Cforward hforward Pbox Vlog Nlog Mlog baseAmbient hPbox hVlog hNlog hMlog hbox hvolume hnormalizer hmaskLog hbaseAmbient hvbase hnbase hmbase hsites haxes hlabelLog hKbase hcoords hcutoff hperiodLog hrowsAmbient houtputs hheight Qgrid hQgrid Ag hAg hBa hBi Dg vg wg hDg hvg hwg hcube hdegree hrowsD htail hblocks hRv hRiGrid hδw hcoeff haxesGrid hfullAxes hfullOutputs hambientCount hprofileBudget Banalytic hBanalytic hDanalytic hcutoffAnalytic hcoordAnalytic hgridAnalytic Pnum hPnum hI hn hcoeffEarly hRiEarly hVEarly Pproj coarseTarget Ecoarse pGain
    ambientQ ambientBudget τ Pphysical W ξn hW cells poly hp hmem signal hsignal hzero
    lossTarget Psample Rrank Sstride εsample ηsample
    hstridepos hN hτ hPs hX hframe hSstride hSstrideP hεsample hτP hεsampleP hstrideBoundSample
    A hsize hrank hRrank hηsample hamb hAmbientP hjet hηsampleP V
    hPphysical hMkPhysical hmGeometry hcoarseTarget0 hDimPhysical hGPhysical hXPhysical
    hprecision hηprecision hεprecision Amass Aanalytic Fmodel Cgrid Qlog tg pg p
    Pnative hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
    hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hstrideGeometry hτGeometry
    hgain hPprojGain hcoarseTarget hEcoarseGain hlossTarget
    Cproj Vproj Acover coverLog Asample Pmass hcoverAmbient hcoverSample hmassSample
    hCactual hVactual
  obtain ⟨hsmall, hbudget, hsitebudget⟩ := geometry.hbudgets C hC hCbound
  have hσ1 (j) : σ j ≤ 1 := (geometry.hσsmall j).trans geometry.htone
  have hnative := exists_allocatedDetected_spatial_native_source
    (hsm := hsm)
    (τ := τ) (Pphysical := Pphysical)
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (pDetect := pDetect) (qDetect := qDetect) (α := α)
    (hP := geometry.hP) (hMkP := hMkP) (hRP := geometry.hRP)
    (hRi := geometry.hRi) (hσi := geometry.hσi) (hcount := geometry.hcount)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
    (D := D) (target := target) (Pk := Pk) (Prho := Prho) (Qstride := Qstride)
    (Pproj := Pproj) (coarseTarget := coarseTarget) (Ecoarse := Ecoarse) (pGain := pGain)
    geometry.hdimensions geometry.hPk hMkPk geometry.hPrho geometry.htarget hQstride hstride hstrideBound
    geometry.hlength geometry.ρ geometry.t geometry.htone geometry.hs (geometry.hρ _) (geometry.hρ1 _) geometry.hσsmall
    geometry.T geometry.hT geometry.hsource C hC hchart hbudget (geometry.hρlog _)
    geometry.hη0 geometry.hηsmall geometry.siteRadius geometry.hrone hsitebudget Cforward hforward K
    geometry.hK geometry.hradius hPbox hVlog hNlog hMlog hbox hvolume
    hnormalizer hmaskLog hbaseAmbient hvbase hnbase hmbase hsites haxes
    hlabelLog hKbase hcoords hcutoff hperiodLog hrowsAmbient houtputs hheight
    Qgrid hQgrid Ag hAg hBa hBi hDg hvg
    hwg hcube hdegree hrowsD htail hblocks hRv hRiGrid
    hδw hcoeff haxesGrid hfullAxes hfullOutputs hambientCount hprofileBudget hBanalytic
    hDanalytic hcutoffAnalytic hcoordAnalytic hgridAnalytic hPnum hI hn hcoeffEarly
    hRiEarly hVEarly
  have hnative := hnative (Pnative := Pnative) cells poly hp hmem signal hsignal hzero
    (lossTarget := lossTarget) (Psample := Psample) (Rrank := Rrank)
    (Sstride := Sstride) (εsample := εsample) (ηsample := ηsample)
    hstridepos hN hτ hPs hX hframe hSstride hSstrideP hεsample hτP hεsampleP hstrideBoundSample
    hsize hrank hRrank hηsample hamb hAmbientP hjet hηsampleP
    hPphysical hMkPhysical hmGeometry hcoarseTarget0 hDimPhysical hGPhysical hXPhysical
    hprecision hηprecision hεprecision
  exact hnative hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
    hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hstrideGeometry hτGeometry
    hgain hPprojGain hcoarseTarget hEcoarseGain hlossTarget
    Cproj Vproj hcoverAmbient hcoverSample hmassSample hCactual hVactual hσ1 hsmall

include hb o bW μ ν μrows hR hσ in

theorem allocatedPreparedNativeInterfaceGeneral_of_nonempty_geometry
    (hsm : s ≤ m)
    (Pchart D target Pk Prho Qstride : ℝ) (K : ℝ≥0)
    (geometry : Nonempty (AllocatedEarlyNativeSourceGeometryGeneral (s := s) (B := B) (U := U) (basis := basis)
      (S := S) (nX := nX) Pchart P D target Pk Prho Qstride pDetect K)) :
    AllocatedPreparedNativeInterfaceGeneral (B := B) (U := U) (basis := basis)
      (hR := hR) (hσ := hσ) (S := S) (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (pDetect := pDetect) (qDetect := qDetect) (α := α)
      (Q := Q) (hb := hb) (o := o) Pchart P D target Pk Prho Qstride K := by
  obtain ⟨geometry⟩ := geometry
  exact allocatedPreparedNativeInterfaceGeneral_of_geometry
    (hsm := hsm)
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (pDetect := pDetect) (qDetect := qDetect) (α := α)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
    Pchart D target Pk Prho Qstride K geometry

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

private theorem allocatedAffineCoveredComparison_instances
    {m : ℕ} {G : Type} [fG : Fintype G] [dG : DecidableEq G]
    {I : Fin m → Type} [fI : ∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [fB : ∀ a, Fintype (B a)]
    {α : Type} [fα : Fintype α] [dα : DecidableEq α] {O : Fin m → Type}
    {dB₁ dB₂ : ∀ a, DecidableEq (B a)}
    {fO₁ fO₂ : ∀ j, Fintype (O j)} {dO₁ dO₂ : ∀ j, DecidableEq (O j)}
    {rows : ∀ j, O j → Finset α} {δ η : ℝ}
    {ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0} {t : ℝ} {htone : t ≤ 1}
    (h : @AllocatedAffineCoveredComparison.{0,0,0,0,0,0,0} m G fG dG I fI n B fB dB₁
      α fα dα O fO₁ dO₁ rows δ η ρ t htone) :
    @AllocatedAffineCoveredComparison.{0,0,0,0,0,0,0} m G fG dG I fI n B fB dB₂
      α fα dα O fO₂ dO₂ rows δ η ρ t htone := by
  have hB : dB₁ = dB₂ := Subsingleton.elim _ _
  have hF : fO₁ = fO₂ := Subsingleton.elim _ _
  have hO : dO₁ = dO₂ := Subsingleton.elim _ _
  cases hB
  cases hF
  cases hO
  exact @h

theorem allocatedEarlyNativeSourceGeometryGeneral_of_fields
    {m s nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (Pchart P D target Pk Prho Qstride pDetect : ℝ) (K : ℝ≥0)
    (hP : 0 ≤ P)
    (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D)
    (hPk : 0 ≤ Pk) (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target (pDetect + 1)
      (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value)
    (η : ℝ) (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{0,0,0,0,0,0,0} (G := G) B
      (fun j : Fin m => (Subtype.val : boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) → Finset (Fin (s + 1))))
      (Real.exp (-(pDetect + 1))) η ρ t htone)
    (hρ : ∀ partition, 0 < ρ partition)
    (hρ1 : ∀ partition, ρ partition ≤ 1)
    (hρlog : ∀ partition, (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho)
    (hσsmall : ∀ j, σ j ≤ t)
    (T : Fin m → ℝ)
    (hT : ∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
          ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (siteRadius : ℝ≥0) (hrone : 1 ≤ siteRadius)
    (hradius : ∀ j, (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card * T j ≤ (siteRadius : ℝ))
    (hbudgets : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp Pchart) →
      (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
      (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
      (∀ j, ((boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin (s + 1))) *
          (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4))
    (hK : ∀ j, (R j)⁻¹ ≤ K) :
    Nonempty (AllocatedEarlyNativeSourceGeometryGeneral (s := s) (B := B)
      (U := U) (basis := basis) (S := S) (nX := nX)
      Pchart P D target Pk Prho Qstride pDetect K) := by
  refine ⟨{
    hP := hP
    hRP := hRP
    hRi := hRi
    hσi := hσi
    hcount := hcount
    hdimensions := hdimensions
    hPk := hPk
    hPrho := hPrho
    htarget := htarget
    hlength := hlength
    η := η
    hη0 := hη0
    hηsmall := hηsmall
    ρ := ρ
    t := t
    htone := htone
    hs := ?_
    hρ := hρ
    hρ1 := hρ1
    hρlog := hρlog
    hσsmall := hσsmall
    T := T
    hT := hT
    hsource := hsource
    siteRadius := siteRadius
    hrone := hrone
    hradius := hradius
    hbudgets := hbudgets
    hK := hK }⟩
  exact @allocatedAffineCoveredComparison_instances m G _ _ I _ n B _
    (Fin (s + 1)) _ _ (fun j => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type))
    _ _ _ _ _ _ _ (Real.exp (-(pDetect + 1))) η ρ t htone (@hs)

private theorem allocatedAffineLengthLog_prepared_density_fin
    (m nX : ℕ) (D P Prho Pk target p Qstride : ℝ) :
    Real.exp (allocatedAffineLengthLog m D P Prho Pk target (p + 1)
      (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤
    Real.exp (allocatedAffineLengthLog m D P Prho Pk target (p + 2)
      (((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride)) := by
  simp only [Fintype.card_fin]
  exact Real.exp_le_exp.mpr (allocatedAffineLengthLog_prepared_density m D P Prho Pk target p _)

private theorem preparedComparison_eta_bound (target cost : ℝ) :
    Real.exp (-(target + cost + 5)) ≤ Real.exp (-(target + 1 + cost + 4)) := by
  apply Real.exp_le_exp.mpr
  linarith only

theorem exists_preparedModularGeneralCanonicalSource (m s Cdetect : ℕ) :
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    let Cgeom := Classical.choose (exists_detected_canonical_native_source_geometry.{0,0,0,0,0} m s Cdetect)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {P pSlice u Qstride Eextra : ℝ},
      0 < m → ∀ hs : s ≤ m, 0 ≤ P → 0 ≤ Eextra → (M : ℝ) ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Palloc := (P + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc s hs
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := Palloc + (2 * Palloc + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      let _T := allocatedIdealCoverSupport (G := G) B rowSets
      let _siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let target := gainLog + 32 + Eextra
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
      let F := pDetect + 2
      let _Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let geometryBudget := (Palloc + Eextra + Cgeom) ^ Cgeom
      let totalBudget := (P + Eextra + C) ^ C
      P ≤ Palloc ∧ pnum ≤ Palloc ∧ geometryBudget ≤ totalBudget ∧
      (s + 1) * (s + 3) ≤ Fintype.card G ∧
      (∀ h : ℕ, h ≤ m → h * Jalloc ≤ Fintype.card G) ∧
      (∀ a : LayerSamplerAxis I n, Jalloc ≤ Fintype.card (B a)) ∧
      (∀ a : LayerSamplerAxis I n, (rowSets a.1).card ≤ Fintype.card (B a)) ∧
      (∀ i, (selection i).val = i.val) ∧
      (∀ inactive : LayerSamplerAxis I n → Prop,
        (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput (Fin nX) I inactive j)) ≤
          nX + m * M) ∧
      ⌈2 * ((modularInitialRankStrength m (nX + m * M) : ℝ) + (nX + m * M : ℕ) + 10) /
        modularRankSmallBallExponent m⌉₊ ≤ Jalloc ∧
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ geometryBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      pModel ∈ Set.Icc 0 geometryBudget ∧ pDetect ∈ Set.Icc 0 geometryBudget ∧
      aDetect ∈ Set.Icc 0 geometryBudget ∧ target ∈ Set.Icc 0 geometryBudget ∧
      D ∈ Set.Icc 0 geometryBudget ∧ gainLog ∈ Set.Icc 0 geometryBudget ∧
      Pk ∈ Set.Icc 0 geometryBudget ∧ Prho ∈ Set.Icc 0 geometryBudget ∧
      Ptail ∈ Set.Icc 0 geometryBudget ∧
      (∀ Vtail : Fin m → ℝ≥0, (∀ j, (Vtail j : ℝ) ≤ Real.exp Palloc) →
        (probabilityProfileLipschitz : ℝ) ≤ Real.exp Palloc →
        let Ctail := 4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j)
        let α := allocatedModelUnitThreshold u pModel
          (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) Ctail
        Ctail ≤ Real.exp pModel ∧ Real.exp (-aDetect) ≤ α) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ {W Qw : ℝ}, 1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        let Pscale := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          Pscale ∈ Set.Icc 0 geometryBudget ∧ Pk ≤ Pscale ∧
          (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog geometryBudget Qw) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          Nonempty (AllocatedEarlyNativeSourceGeometryGeneral (B := B) (U := U)
            (basis := basis) (S := S) (s := s) (nX := nX)
            Palloc Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1)) ∧
            (scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  intro Aalloc Cgeom
  obtain ⟨C, hC, hgeometry⟩ := exists_preparedModularWitnessCanonicalGeometry.{0,0} m s Cdetect
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord P pSlice u Qstride Eextra hm hs hP hExtra hM hpSlice hu hQstride hnX
    Jalloc pnum Palloc G I n B selection A Pearly rowSets T siteRadius pModel pDetect aDetect D
    gainLog target Pk F Tmod δ E η Prho Ptail K geometryBudget totalBudget
  obtain ⟨hPalloc, hpnum, hGeometryBudget, hcapacity, hkernelAllocation, hblockAllocation,
      hblockRows, hselection, houtputCount, hthreshold,
      pRadius, R, hpRadius, hpRadiusBudget, hR, hrone, hT0, hTideal, hTsource, hTradius,
      hTbound, hrbound, hTbudget, hrbudget, hsmall, hdimensions, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      ρ, hρ, t, ht, htone, htPtail, htbudget, hcomparison, hsamplers⟩ :=
    hgeometry L hCoord hm hs hP hExtra hM hpSlice hu hQstride hnX
  refine ⟨hPalloc, hpnum, hGeometryBudget, hcapacity, hkernelAllocation, hblockAllocation,
    hblockRows, hselection, houtputCount, hthreshold,
    pRadius, R, hpRadius, hpRadiusBudget, hR,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, ?_, t, ht, htone, ?_⟩
  · intro Vtail hVtail hprofile Ctail α
    obtain ⟨_, _, _, _, _, hcap, _, _, _, _, _, _, _, hα, _, _⟩ :=
      preparedModularCanonicalDetector_early_cap L Jalloc A hCoord (hP.trans hPalloc)
        hpnum hpSlice.1 hu.1 R Vtail (fun j => (hR j).1)
        (fun j => (hR j).2.2) hpRadius.2 hVtail hprofile
    exact ⟨hcap, hα⟩
  intro W Qw hW hQw hWexp J _ U basis Pscale
  obtain ⟨hPscale, hScaleLog, S, hRinv, htinv', hcount, hlength, hS, hwidth, hcutoff⟩ :=
    hsamplers hW hQw hWexp U basis
  have hD1 : 1 ≤ D := by
    have hdim := (allocatedComparisonDimension_bounds m (show 0 ≤ pnum from Nat.cast_nonneg _)).2.1
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
    exact hm1.trans hdim
  have hkTail : Pk ≤ Ptail :=
    prepared_affineProfileToleranceEnvelope_kernel_bound hm
      canonicalSublevelCutoffLip canonicalTransitionLip hD1 hPk.1 htarget.1 hDetect.1
  have hkScale : Pk ≤ Pscale := hkTail.trans (le_add_of_nonneg_left hpRadius.1)
  refine ⟨S, hPscale, hkScale, hS, hwidth, ?_, ?_⟩
  · refine allocatedEarlyNativeSourceGeometryGeneral_of_fields B U basis S
      Palloc Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))
      hPscale.1 (fun j => (hR j).2.1.trans (Real.one_le_exp hPscale.1))
      hRinv htinv' hcount hdimensions hPk.1 hPrho.1 htarget.1 ?_
      η (Real.exp_pos _).le ?_ ρ t htone (@hcomparison)
      (fun partition => (hρ partition).1) (fun partition => (hρ partition).2.1)
      (fun partition => (hρ partition).2.2.1) (fun _ => le_rfl)
      T hTideal hTsource siteRadius hrone hTradius hsmall
      (fun j => (hR j).2.2.trans (Real.le_coe_toNNReal _))
    · exact (allocatedAffineLengthLog_prepared_density_fin
        m nX D Pscale Prho Pk target pDetect Qstride).trans hlength
    · exact preparedComparison_eta_bound target (D * ((m * 2 ^ (m + 1) : ℕ) * Pk))
  · intro α hα
    exact ⟨slicedDetectionGain_lower s Cdetect _ hα,
      slicedDetection_kernel_cutoff_bound s Cdetect _ G hDetect.1 hDetect.1 hAlog.1 hα,
      hcutoff α hα⟩

theorem exists_preparedModularGeneralCanonicalEarlyParameters (m s Cdetect : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type) [∀ b, Fintype (B b)] [∀ b, DecidableEq (B b)]
      {P pnum pSlice u Qstride : ℝ} {nX : ℕ},
      0 < m → s ≤ m → 0 ≤ P → pnum ∈ Set.Icc 0 P →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum →
      (∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) → (∀ j, (n j : ℝ) ≤ pnum) →
      (∀ b : LayerSamplerAxis I n,
        (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b)) →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Aradius := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := P + (2 * P + Aradius) ^ Aradius + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog s Cdetect
        (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
      let budget := (P + A) ^ A
      P ≤ budget ∧ Pearly ∈ Set.Icc 0 budget ∧ pModel ∈ Set.Icc 0 budget ∧
        pDetect ∈ Set.Icc 0 budget ∧ aDetect ∈ Set.Icc 0 budget ∧
        D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget := by
  obtain ⟨A, hA, hgeometry⟩ := exists_detected_canonical_native_source_geometry.{0,0,0,0,0} m s Cdetect
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ n B _ _ P pnum pSlice u Qstride nX hm hs hP hnum hvars hI hn hblocks
    hpSlice hu hQstride hnX Aradius Pearly pModel pDetect aDetect D gainLog Pk budget
  have hactual := hgeometry (G := G) B (Eextra := 0) hm hs hP
    (le_refl 0) hnum hvars hI hn hblocks hpSlice hu hQstride hnX
  obtain ⟨pRadius, R, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hPEarly,
    hEarlyBudget, hModel, hDetect, hAlog, _, hD, hGain, hPk, _⟩ := hactual
  have hEarly : Pearly ∈ Set.Icc 0 budget := by
    exact ⟨hP.trans hPEarly, by simpa only [add_zero] using hEarlyBudget⟩
  refine ⟨hPEarly.trans hEarly.2, hEarly, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [add_zero] using hModel
  · simpa only [add_zero] using hDetect
  · simpa only [add_zero] using hAlog
  · simpa only [add_zero] using hD
  · simpa only [add_zero] using hGain
  · simpa only [add_zero] using hPk

theorem exists_preparedModularGeneralCanonicalPhysicalSource (m s Cdetect : ℕ) :
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    let Cgeom := Classical.choose (exists_detected_canonical_native_source_geometry.{0,0,0,0,0} m s Cdetect)
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)
    let Cphysical := Classical.choose (exists_detectedCanonicalPhysicalBudget m Aearly Cgeom)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {P pSlice u Qstride : ℝ},
      0 < m → ∀ hs : s ≤ m, 0 ≤ P → (M : ℝ) ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Palloc := (P + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc s hs
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := Palloc + (2 * Palloc + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      let _T := allocatedIdealCoverSupport (G := G) B rowSets
      let _siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
      let Qearly := (Palloc + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let coarseTarget := gainLog + 32
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
      let τ := Real.exp (-Pphysical)
      let Rspatial := spatialPrimitiveEnvelope Pphysical coarseTarget 0
      let ξLog := 2 * (Rspatial + spatialTupleToleranceLog Rspatial) + 4
      let F := pDetect + 2
      let _Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let geometryBudget := (Palloc + Eextra + Cgeom) ^ Cgeom
      let sourceBudget := (Palloc + Cphysical) ^ Cphysical
      let totalBudget := (P + C) ^ C
      P ≤ Palloc ∧ pnum ≤ Palloc ∧ geometryBudget ≤ sourceBudget ∧ sourceBudget ≤ totalBudget ∧
      Pphysical ∈ Set.Icc 0 sourceBudget ∧ coarseTarget ∈ Set.Icc 0 sourceBudget ∧
      ξLog ∈ Set.Icc 0 sourceBudget ∧ 0 ≤ Eextra ∧
      coarseTarget + coefficientErrorSpatialLog Pphysical + 8 = target ∧
      0 < τ ∧ τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 ∧ 1 / τ = Real.exp Pphysical ∧
      (s + 1) * (s + 3) ≤ Fintype.card G ∧
      (∀ h : ℕ, h ≤ m → h * Jalloc ≤ Fintype.card G) ∧
      (∀ a : LayerSamplerAxis I n, Jalloc ≤ Fintype.card (B a)) ∧
      (∀ a : LayerSamplerAxis I n, (rowSets a.1).card ≤ Fintype.card (B a)) ∧
      (∀ i, (selection i).val = i.val) ∧
      (∀ inactive : LayerSamplerAxis I n → Prop,
        (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput (Fin nX) I inactive j)) ≤
          nX + m * M) ∧
      ⌈2 * ((modularInitialRankStrength m (nX + m * M) : ℝ) + (nX + m * M : ℕ) + 10) /
        modularRankSmallBallExponent m⌉₊ ≤ Jalloc ∧
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ geometryBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      pModel ∈ Set.Icc 0 geometryBudget ∧ pDetect ∈ Set.Icc 0 geometryBudget ∧
      aDetect ∈ Set.Icc 0 geometryBudget ∧ target ∈ Set.Icc 0 geometryBudget ∧
      D ∈ Set.Icc 0 geometryBudget ∧ gainLog ∈ Set.Icc 0 geometryBudget ∧
      Pk ∈ Set.Icc 0 geometryBudget ∧ Prho ∈ Set.Icc 0 geometryBudget ∧
      Ptail ∈ Set.Icc 0 geometryBudget ∧
      (∀ Vtail : Fin m → ℝ≥0, (∀ j, (Vtail j : ℝ) ≤ Real.exp Palloc) →
        (probabilityProfileLipschitz : ℝ) ≤ Real.exp Palloc →
        let Ctail := 4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j)
        let α := allocatedModelUnitThreshold u pModel
          (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) Ctail
        Ctail ≤ Real.exp pModel ∧ Real.exp (-aDetect) ≤ α) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ {W Qw : ℝ}, 1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        let Pscale := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          Pscale ∈ Set.Icc 0 geometryBudget ∧ Pk ≤ Pscale ∧
          (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog geometryBudget Qw) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          Nonempty (AllocatedEarlyNativeSourceGeometryGeneral (B := B) (U := U)
            (basis := basis) (S := S) (s := s) (nX := nX)
            Palloc Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1)) ∧
            (scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  intro Aalloc Cgeom Aearly Cphysical
  obtain ⟨C, hC, htotal⟩ := exists_shiftedPower_triple_composition_budget Aalloc Cphysical 1
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord P pSlice u Qstride hm hs hP hM hpSlice hu hQstride hnX
    Jalloc pnum Palloc G I n B selection A Pearly rowSets T siteRadius pModel pDetect aDetect D
    gainLog Pk Qearly Pphysical coarseTarget Eextra target τ Rspatial ξLog F Tmod δ E η Prho Ptail K
    geometryBudget sourceBudget totalBudget
  obtain ⟨hPalloc, hJalloc, hnum, hsum⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetectorAllocationBudget m)).2 hP hM hnX
  have hAlloc0 : 0 ≤ Palloc := hP.trans hPalloc
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hCoord
  have hblocks (a : LayerSamplerAxis I n) :
      (boundedBooleanJetRows (Fin (s + 1)) (a.1.val + 1)).card ≤ Fintype.card (B a) := by
    calc
      _ = Fintype.card (BoundedBooleanJet (Fin (s + 1)) (a.1.val + 1)) :=
        (Fintype.card_coe _).symm.trans (Fintype.card_congr (boundedBooleanJetRowsEquiv _ _))
      _ ≤ _ := enlargedPreparedCommonSamplerBlock_jets L Jalloc s hs a
  obtain ⟨hPQ, hEarlyQ, hModelQ, hDetectQ, hAQ, hDQ, hGainQ, hPkQ⟩ :=
    (Classical.choose_spec (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)).2
      (G := G) B hm hs hAlloc0 hnum (Nat.cast_le.mpr hvars)
      (fun j => Nat.cast_le.mpr (hI j)) (fun j => Nat.cast_le.mpr (hn j))
      hblocks ⟨hpSlice.1, hpSlice.2.trans hPalloc⟩ ⟨hu.1, hu.2.trans hPalloc⟩
      ⟨hQstride.1, hQstride.2.trans hPalloc⟩ (hnX.trans hPalloc)
  obtain ⟨hExtra, hprecision, hτ, hτhalf, hτdim, hτinv,
      hPhysBudget, hCoarseBudget, hExtraBudget, hTargetBudget, hξBudget, hGeomBudget⟩ :=
    (Classical.choose_spec (exists_detectedCanonicalPhysicalBudget m Aearly Cgeom)).2
      nX hAlloc0 hPkQ.1 hQstride.1 hGainQ.1 hPkQ.2
      (hQstride.2.trans (hPalloc.trans hPQ)) hGainQ.2 (hnX.trans (hPalloc.trans hPQ))
  have hPhys0 : 0 ≤ Pphysical := by
    change 0 ≤ Qearly + Pk + Qstride + (nX : ℝ) + (m + 1 : ℕ) + 8
    have hQ0 : 0 ≤ Qearly := pow_nonneg (add_nonneg hAlloc0 (Nat.cast_nonneg _)) _
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hQ0 hPkQ.1)
      hQstride.1) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (by norm_num)
  have hCoarse0 : 0 ≤ coarseTarget := by
    change 0 ≤ gainLog + 32
    linarith only [hGainQ.1]
  have hξ0 : 0 ≤ ξLog := by
    have hRsp := (spatialPrimitiveEnvelope_bounds hPhys0 hCoarse0 (le_refl 0)).1
    have htsp := spatialTupleToleranceLog_nonneg hRsp
    change 0 ≤ 2 * (Rspatial + spatialTupleToleranceLog Rspatial) + 4
    linarith only [hRsp, htsp]
  have htotalBudget : sourceBudget ≤ totalBudget := by
    have h := htotal hP
    simp only [Nat.cast_one, pow_one] at h
    exact (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans h
  obtain ⟨_, _, _, hcapacity, hkernelAllocation, hblockAllocation, hblockRows,
      hselection, houtputCount, hthreshold, hsource⟩ :=
    (Classical.choose_spec (exists_preparedModularGeneralCanonicalSource m s Cdetect)).2
      L hCoord hm hs hP hExtra hM hpSlice hu hQstride hnX
  exact ⟨hPalloc, hnum.2, hGeomBudget, htotalBudget, ⟨hPhys0, hPhysBudget⟩,
    ⟨hCoarse0, hCoarseBudget⟩, ⟨hξ0, hξBudget⟩, hExtra, hprecision,
    hτ, hτhalf, hτdim, hτinv, hcapacity, hkernelAllocation, hblockAllocation,
    hblockRows, hselection, houtputCount, hthreshold, hsource⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

theorem preparedModularGeneralProductivity_early_gain (m s Cdetect : ℕ) :
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type) [∀ b, Fintype (B b)] [∀ b, DecidableEq (B b)]
      {P pnum pSlice u Qstride : ℝ} {nX : ℕ},
      0 < m → s ≤ m → 0 ≤ P → pnum ∈ Set.Icc 0 P →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum →
      (∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) → (∀ j, (n j : ℝ) ≤ pnum) →
      (∀ b : LayerSamplerAxis I n,
        (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b)) →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Aradius := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := P + (2 * P + Aradius) ^ Aradius + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog s Cdetect
        (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let budget := (P + Aearly) ^ Aearly
      P ≤ budget ∧ gainLog ≤ budget := by
  intro Aearly G _ _ I _ n B _ _ P pnum pSlice u Qstride nX
    hm hs hP hnum hvars hI hn hblocks hpSlice hu hQstride hnX
    Aradius Pearly pModel pDetect aDetect gainLog budget
  have h := (Classical.choose_spec
    (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)).2
      (G := G) B hm hs hP hnum hvars hI hn hblocks hpSlice hu hQstride hnX
  exact ⟨h.1, h.2.2.2.2.2.2.1.2⟩

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Geometry.SharedWidthAllocatedCanonicalSpatialNativeSource

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable abbrev allocatedDetectedGain (s variableCount : ℕ)
    (Pdetect : Polynomial ℕ) (p q α : ℝ) : ℝ :=
  (Real.exp (-((5 * p + 20) * variableCount + p + 2)) * (α / 2)) *
    Real.exp (-((q + sampledSupportedSlicedDetectionConstant s Pdetect) ^
      sampledSupportedSlicedDetectionConstant s Pdetect)) ^ (2 ^ (s + 1))

noncomputable abbrev allocatedDetectedKernelCutoff (s : ℕ) (G : Type) [Fintype G]
    (variableCount : ℕ) (Pdetect : Polynomial ℕ) (p q α : ℝ) : ℕ :=
  scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
    (allocatedDetectedGain s variableCount Pdetect p q α / 2)

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
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

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

include hb o bW μ ν μrows hR hσ hP hMkP hRP hRi hσi hcount in

theorem exists_allocatedDetected_spatial_native_source
    (hsm : s ≤ m)
    {D target Pk Prho Qstride : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D)
    (hPk : 0 ≤ Pk)
    (hMkPk : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho)
    (htarget : 0 ≤ target)
    (hQstride : 0 ≤ Qstride)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target (pDetect + 1) (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value)
    {η : ℝ}
    (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (t : ℝ)
    (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{0, 0, _, _, _, _, _} (G := G) B rows (Real.exp (-(pDetect + 1))) η ρ t htone)
    (hρ : 0 < ρ grid)
    (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (T : Fin m → ℝ)
    (hT : ∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) * ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ)
    (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (siteRadius : ℝ≥0)
    (hrone : 1 ≤ siteRadius)
    (hsitebudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0)
    (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ))
    {Pbox Vlog Nlog Mlog baseAmbient : ℝ}
    (hPbox : 0 ≤ Pbox)
    (hVlog : 0 ≤ Vlog)
    (hNlog : 0 ≤ Nlog)
    (hMlog : 0 ≤ Mlog)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hvolume : allocatedFullGridNaturalVolume B U basis S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖((allocatedProductIdealNormalizer B U basis S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp Nlog)
    (hmaskLog : (Fintype.card (LayerSamplerAxis I n) : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * (((m + 1 : ℕ) : ℝ) * Pk)) ≤ Mlog)
    (hbaseAmbient : 0 ≤ baseAmbient)
    (hvbase : Vlog ≤ baseAmbient)
    (hnbase : Nlog ≤ baseAmbient)
    (hmbase : Mlog ≤ baseAmbient)
    (hsites : (Fintype.card (Finset (Fin (s + 1))) : ℝ) ≤ baseAmbient)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ baseAmbient)
    (hlabelLog : (∑ j, (n j : ℝ) * (((m + 1 : ℕ) : ℝ) * Pk)) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (((m + 1 : ℕ) : ℝ) * Pk) ≤ baseAmbient)
    (hKbase : (K : ℝ) ≤ Real.exp baseAmbient)
    (hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp baseAmbient)
    (hperiodLog : ((m + 1 : ℕ) : ℝ) * Pk ≤ baseAmbient)
    (hrowsAmbient : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ baseAmbient)
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp baseAmbient)
    (Qgrid : ℝ≥0)
    (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U basis S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U basis S a).1 (allocatedGridIntegerAxis B U basis S a).2) : ℝ) + 1) ≤ Qgrid)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg : ℝ}
    (hDg : 0 ≤ Dg)
    (hvg : 0 ≤ vg)
    (hwg : 0 ≤ wg)
    (hcube : (Fintype.card (Fin (s + 1)) : ℝ) ≤ Dg)
    (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg)
    (hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : pDetect + 1 ≤ wg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ Dg)
    (hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Dg)
    (hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ Dg)
    (hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ Dg)
    (hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ Dg)
    {Banalytic : ℝ}
    (hBanalytic : 0 ≤ Banalytic)
    (hDanalytic : Dg ≤ Banalytic)
    (hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Banalytic)
    (hcoordAnalytic : ((K * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Banalytic)
    (hgridAnalytic : (Qgrid : ℝ) ≤ Real.exp Banalytic)
    {Pnum : ℝ}
    (hPnum : 0 ≤ Pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum)
    (hn : ∀ j, (n j : ℝ) ≤ Pnum)
    (hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
    (hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
    (hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Real.exp Pnum)
    {Pproj coarseTarget Ecoarse pGain : ℝ}
    :
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
    (hPhysicalNonneg : 0 ≤ Pphysical) → (hMkPhysicalBound : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pphysical) →
    (hmPhysicalBound : ((m + 1 : ℕ) : ℝ) ≤ Pphysical) → (hCoarseNonneg : 0 ≤ coarseTarget) →
    (hDimPhysicalBound : (((s + 1) + 1 : ℕ) : ℝ) ≤ Pphysical) →
    (hGPhysicalBound : (Fintype.card G : ℝ) ≤ Pphysical) →
    (hXPhysicalBound : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical) →
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
    (∀ j, σ j ≤ 1) →
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) →
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
            (fun u => signal u.val) (fun u => star (twistData.eval N poly u.val) * Fnative u)‖ := by
  intro ambientQ ambientBudget τ Pphysical W ξn hW cells poly hp hmem signal hsignal hzero
    lossTarget Psample Rrank Sstride εsample ηsample
    hstridepos hN hτ hPs hX hframe hSstride hSstrideP hεsample hτP hεsampleP hstrideBoundSample
    A hsize hrank hRrank hηsample hamb hAmbientP hjet hηsampleP V
    hPphysical hMkPhysical hmGeometry hcoarseTarget0 hDimPhysical hGPhysical hXPhysical
    hprecision hηprecision hεprecision Amass Aanalytic Fmodel Cgrid Qlog tg pg p
    Pnative hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
    hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hstrideGeometry hτGeometry
    hgain hPprojGain hcoarseTarget hEcoarseGain hlossTarget
    Cproj Vproj Acover coverLog Asample Pmass hcoverAmbient hcoverSample hmassSample
    hCactual hVactual hσ1 hsmall hXmass hframeMass hstrideMass hτMass
    AmassWindow hsizeMass hRrankMass hambMass hjetMass hvars
    hPproj hmProj hGproj hLproj hperiodP
    hKproj hWproj hRproj hσproj hcountProj hIproj hnProj hJproj hProfileProj hCproj hVproj
    hXproj hFrameProj hStrideProj hτProj hξProj Aproj hSizeProj hRankProj
    Pside hProjSide hCapSide hpSide htargetSide hside hCells bases hbases hξn hmass htotal Path pathLaw
    Tdetect _ _ e he Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstepdetect hslices hpDetect hqDetect hdenseDetect hdimensionDetect hcomplexity hcap
    hα hαone hmeshDetect hthreshold hdetected hGdetect hkernel
    Cbudget Bbudget Anorm Anative Abudget budget
  have hsignalAll (u) : ‖signal u‖ ≤ 1 := by
    by_cases hu : u ∈ integerBox N
    · exact hsignal u hu
    · simp only [hzero u hu, norm_zero, zero_le_one]
  have hF : 0 ≤ pDetect + 1 := by positivity
  obtain ⟨hδ, _hδ1, hδF, htg, hpg, Tg, hTg, hgrid⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetector_grid_parameters.{0} m (s + 1) Ag)).2
      (nX := nX) hPk hQstride hpDetect
  have hδw' : (Real.exp (-(pDetect + 1)))⁻¹ ≤ Real.exp wg :=
    hδF.trans (Real.exp_le_exp.mpr hδw)
  have hfound := allocatedOriginalPathLaw_canonical_period_source (s := s)
    B U basis hb o hR hσ S (Fin nX) poly hmem N hN hW hτ hξn
    stride cells hmass bases hbases htotal Pdetect e he Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstepdetect hslices pDetect qDetect hpDetect hqDetect hdenseDetect hdimensionDetect hcomplexity hcap
    signal hsignalAll α hα hαone hmeshDetect hthreshold hdetected selection hGdetect hkernel hstridepos
  obtain ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubsetAll, hdenseAll, hstepBound,
    x, hgood, hMk, hperiodPos, hperiodBound, r₀, hcell, hsubset, hdetectedTuple,
    y₀, hy₀, _hyCube, _hyAxis, _hselected⟩ := hfound
  let period := kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hgood m)
  have : NeZero period := ⟨hperiodPos.ne'⟩
  let modulus := residueRefinedPeriod period stride
  let Hnative := fun j : PrincipalTupleIndex B (layerSamplerDegree I n) => H₀ (Sum.inr j)
  let stepnative := fun _ : PrincipalTupleIndex B (layerSamplerDegree I n) => step₀
  let cnative := fun j : PrincipalTupleIndex B (layerSamplerDegree I n) => c₀ (Sum.inr j)
  have hHnative (j) : 0 < Hnative j := hH₀ (Sum.inr j)
  have hdenseNative (j : Tuple) :
      Real.exp (-(pDetect + 1)) * L j ≤
        ((integerProgressionSupport
          (c₀ (Sum.inr (Sigma.mk j.1.val j.2))) (step₀ : ℤ)
          (H₀ (Sum.inr (Sigma.mk j.1.val j.2)))).card : ℝ) := by
    rw [card_integerProgressionSupport _ _ _ hstep₀]
    exact hdenseAll (Sum.inr (Sigma.mk j.1.val j.2))
  have hperiodBounds := canonicalPeriod_primitive_bounds
    (LayerSamplerAxis I n) n selectedRows Q hMkPk hperiodBound
  have hmask := hperiodBounds.2.1.trans (Real.exp_le_exp.mpr hmaskLog)
  have hlabels := hperiodBounds.2.2.trans (Real.exp_le_exp.mpr hlabelLog)
  have hpbase := hperiodBounds.1.trans (Real.exp_le_exp.mpr hperiodLog)
  obtain ⟨hQTg, hPg, hcP, hsP, hstrideGrid⟩ :=
    hgrid stride hMkPk hperiodPos hperiodBound hstridepos hstrideBound
  have hstrideGrid' (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
      ((stepnative j * modulus : ℕ) : ℝ) ≤ Real.exp pg := by
    exact hstrideGrid (Y := PrincipalTupleIndex B (layerSamplerDegree I n))
      stepnative (fun _ => hstepBound) j
  have hnative := exists_allocatedCanonicalSlice_spatial_native_source
    (s := s) (nX := nX) (τ := τ) (Pphysical := Pphysical) (gain := (allocatedDetectedGain s (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) / 2) (Pproj := Pproj)
    (coarseTarget := coarseTarget) (Ecoarse := Ecoarse) (pGain := pGain)
    B U basis hR hσ S x hMk selection hgood period stride N rfl modulus rfl
    hP hMkP hRP hRi hσi hcount Q hb o bW Hnative stepnative cnative hHnative hsubset r₀ hcell ν μ μrows
    hdimensions hPk hMkPk hPrho htarget hF hQstride hstride hstrideBound hlength
    ρ t htone hs hρ hρ1 hσsmall (fun _ => hstep₀) hδ hδF hdenseNative
    (by simp only [Fintype.card_fin]; omega) y₀ hy₀
    T hT hsource C hC hchart hbudget hρlog hη0 hηsmall
    siteRadius hrone hsitebudget Cforward hforward K hK hradius
    hPbox hVlog hNlog hMlog hbox hvolume hnormalizer hmask hbaseAmbient hvbase hnbase hmbase
    hsites haxes hlabels hKbase hcoords hcutoff hpbase hrowsAmbient houtputs hheight
    Qgrid hQgrid hδ (fun j => hdenseAll (Sum.inr j)) Tg
    (by simpa only [Fintype.card_fin] using hQTg) (fun _ => hstep₀)
    Ag hAg (Real.exp pg) hPg hcP hsP hstrideGrid'
    hBa hBi hDg hvg hwg htg hpg hcube hdegree hrowsD htail hblocks hRv hRiGrid hδw' hTg hcoeff
    le_rfl haxesGrid hfullAxes hfullOutputs hambientCount hprofileBudget
    hBanalytic hDanalytic hcutoffAnalytic hcoordAnalytic hgridAnalytic
    hPnum hI hn hcoeffEarly hRiEarly hVEarly
  have hnative := hnative (Pnative := Pnative) cells poly hp hmem signal hsignal hzero
    (lossTarget := lossTarget) (Psample := Psample) (Rrank := Rrank)
    (Sstride := Sstride) (εsample := εsample) (ηsample := ηsample)
    hstridepos hN hτ hPs hX hframe hSstride hSstrideP hεsample hτP hεsampleP hstrideBoundSample
    hsize hrank hRrank hηsample hamb hAmbientP hjet hηsampleP
    hPphysical hMkPhysical hmGeometry hcoarseTarget0 hDimPhysical hGPhysical hXPhysical
    hprecision hηprecision hεprecision
  have hnative := hnative (Pside := Pside) hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
    hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hstrideGeometry hτGeometry
    hgain hPprojGain hcoarseTarget hEcoarseGain hlossTarget
    Cproj Vproj hcoverAmbient hcoverSample hmassSample hCactual hVactual hσ1 hsmall
    hXmass hframeMass hstrideMass hτMass hsizeMass hRrankMass hambMass hjetMass hvars
    hPproj hmProj hGproj hLproj hperiodP hKproj hWproj hRproj hσproj hcountProj hIproj hnProj hJproj
    hProfileProj hCproj hVproj hXproj hFrameProj hStrideProj hτProj hξProj hSizeProj hRankProj
  exact hnative hProjSide hCapSide hpSide htargetSide hside hCells bases hbases hmass hdetectedTuple

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
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

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

include hb o bW μ ν μrows hR hσ hP hMkP hRP hRi hσi hcount in

theorem exists_allocatedDetected_spatial_native_source_sharedWidth
    (hsm : s ≤ m)
    {D target Pk Prho Qstride : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D)
    (hPk : 0 ≤ Pk)
    (hMkPk : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho)
    (htarget : 0 ≤ target)
    (hQstride : 0 ≤ Qstride)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target (pDetect + 1) (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value)
    {η : ℝ}
    (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (t : ℝ)
    (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{0, 0, _, _, _, _, _} (G := G) B rows (Real.exp (-(pDetect + 1))) η ρ t htone)
    (hρ : 0 < ρ grid)
    (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (T : Fin m → ℝ)
    (hT : ∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) * ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ)
    (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (siteRadius : ℝ≥0)
    (hrone : 1 ≤ siteRadius)
    (hsitebudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0)
    (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ))
    {Pbox Vlog Nlog Mlog baseAmbient : ℝ}
    (hPbox : 0 ≤ Pbox)
    (hVlog : 0 ≤ Vlog)
    (hNlog : 0 ≤ Nlog)
    (hMlog : 0 ≤ Mlog)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hvolume : allocatedFullGridNaturalVolume B U basis S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖((allocatedProductIdealNormalizer B U basis S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp Nlog)
    (hmaskLog : (Fintype.card (LayerSamplerAxis I n) : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * (((m + 1 : ℕ) : ℝ) * Pk)) ≤ Mlog)
    (hbaseAmbient : 0 ≤ baseAmbient)
    (hvbase : Vlog ≤ baseAmbient)
    (hnbase : Nlog ≤ baseAmbient)
    (hmbase : Mlog ≤ baseAmbient)
    (hsites : (Fintype.card (Finset (Fin (s + 1))) : ℝ) ≤ baseAmbient)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ baseAmbient)
    (hlabelLog : (∑ j, (n j : ℝ) * (((m + 1 : ℕ) : ℝ) * Pk)) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (((m + 1 : ℕ) : ℝ) * Pk) ≤ baseAmbient)
    (hKbase : (K : ℝ) ≤ Real.exp baseAmbient)
    (hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp baseAmbient)
    (hperiodLog : ((m + 1 : ℕ) : ℝ) * Pk ≤ baseAmbient)
    (hrowsAmbient : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ baseAmbient)
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp baseAmbient)
    (Qgrid : ℝ≥0)
    (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U basis S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U basis S a).1 (allocatedGridIntegerAxis B U basis S a).2) : ℝ) + 1) ≤ Qgrid)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg : ℝ}
    (hDg : 0 ≤ Dg)
    (hvg : 0 ≤ vg)
    (hwg : 0 ≤ wg)
    (hcube : (Fintype.card (Fin (s + 1)) : ℝ) ≤ Dg)
    (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg)
    (hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : pDetect + 1 ≤ wg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ Dg)
    (hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Dg)
    (hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ Dg)
    (hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ Dg)
    (hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ Dg)
    {Banalytic : ℝ}
    (hBanalytic : 0 ≤ Banalytic)
    (hDanalytic : Dg ≤ Banalytic)
    (hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Banalytic)
    (hcoordAnalytic : ((K * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Banalytic)
    (hgridAnalytic : (Qgrid : ℝ) ≤ Real.exp Banalytic)
    {Pnum : ℝ}
    (hPnum : 0 ≤ Pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum)
    (hn : ∀ j, (n j : ℝ) ≤ Pnum)
    (hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
    (hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
    (hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Real.exp Pnum)
    {Pproj coarseTarget Ecoarse pGain : ℝ}
    :
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin (s + 1)))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    ∀ {τ Pphysical : ℝ},
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn), ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) Pphysical coarseTarget →
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
    (hPhysicalNonneg : 0 ≤ Pphysical) → (hMkPhysicalBound : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pphysical) →
    (hmPhysicalBound : ((m + 1 : ℕ) : ℝ) ≤ Pphysical) → (hCoarseNonneg : 0 ≤ coarseTarget) →
    (hDimPhysicalBound : (((s + 1) + 1 : ℕ) : ℝ) ≤ Pphysical) →
    (hGPhysicalBound : (Fintype.card G : ℝ) ≤ Pphysical) →
    (hXPhysicalBound : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical) →
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
    (∀ j, σ j ≤ 1) →
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) →
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
      Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{0,0,0,0} m) + Pproj) ≤ (N i : ℝ)) →
    cells.Nonempty → ∀ (bases : Finset (Fin nX → ℤ)), (hbases : bases.Nonempty) →
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
            (fun u => signal u.val) (fun u => star (twistData.eval N poly u.val) * Fnative u)‖ := by
  intro ambientQ ambientBudget τ Pphysical W ξn hξn hξnLe hW cells poly hp hmem signal hsignal hzero
    lossTarget Psample Rrank Sstride εsample ηsample
    hstridepos hN hτ hPs hX hframe hSstride hSstrideP hεsample hτP hεsampleP hstrideBoundSample
    A hsize hrank hRrank hηsample hamb hAmbientP hjet hηsampleP V
    hPphysical hMkPhysical hmGeometry hcoarseTarget0 hDimPhysical hGPhysical hXPhysical
    hprecision hηprecision hεprecision Amass Aanalytic Fmodel Cgrid Qlog tg pg p
    Pnative hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
    hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hstrideGeometry hτGeometry
    hgain hPprojGain hcoarseTarget hEcoarseGain hlossTarget
    Cproj Vproj Acover coverLog Asample Pmass hcoverAmbient hcoverSample hmassSample
    hCactual hVactual hσ1 hsmall hXmass hframeMass hstrideMass hτMass
    AmassWindow hsizeMass hRrankMass hambMass hjetMass hvars
    hPproj hmProj hGproj hLproj hperiodP
    hKproj hWproj hRproj hσproj hcountProj hIproj hnProj hJproj hProfileProj hCproj hVproj
    hXproj hFrameProj hStrideProj hτProj hξProj Aproj hSizeProj hRankProj
    Pside hProjSide hCapSide hpSide htargetSide hside hCells bases hbases hmass htotal Path pathLaw
    Tdetect _ _ e he Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstepdetect hslices hpDetect hqDetect hdenseDetect hdimensionDetect hcomplexity hcap
    hα hαone hmeshDetect hthreshold hdetected hGdetect hkernel
    Cbudget Bbudget Anorm Anative Abudget budget
  have hsignalAll (u) : ‖signal u‖ ≤ 1 := by
    by_cases hu : u ∈ integerBox N
    · exact hsignal u hu
    · simp only [hzero u hu, norm_zero, zero_le_one]
  have hF : 0 ≤ pDetect + 1 := by positivity
  obtain ⟨hδ, _hδ1, hδF, htg, hpg, Tg, hTg, hgrid⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetector_grid_parameters.{0} m (s + 1) Ag)).2
      (nX := nX) hPk hQstride hpDetect
  have hδw' : (Real.exp (-(pDetect + 1)))⁻¹ ≤ Real.exp wg :=
    hδF.trans (Real.exp_le_exp.mpr hδw)
  have hfound := allocatedOriginalPathLaw_canonical_period_source (s := s)
    B U basis hb o hR hσ S (Fin nX) poly hmem N hN hW hτ hξn
    stride cells hmass bases hbases htotal Pdetect e he Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstepdetect hslices pDetect qDetect hpDetect hqDetect hdenseDetect hdimensionDetect hcomplexity hcap
    signal hsignalAll α hα hαone hmeshDetect hthreshold hdetected selection hGdetect hkernel hstridepos
  obtain ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubsetAll, hdenseAll, hstepBound,
    x, hgood, hMk, hperiodPos, hperiodBound, r₀, hcell, hsubset, hdetectedTuple,
    y₀, hy₀, _hyCube, _hyAxis, _hselected⟩ := hfound
  let period := kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hgood m)
  have : NeZero period := ⟨hperiodPos.ne'⟩
  let modulus := residueRefinedPeriod period stride
  let Hnative := fun j : PrincipalTupleIndex B (layerSamplerDegree I n) => H₀ (Sum.inr j)
  let stepnative := fun _ : PrincipalTupleIndex B (layerSamplerDegree I n) => step₀
  let cnative := fun j : PrincipalTupleIndex B (layerSamplerDegree I n) => c₀ (Sum.inr j)
  have hHnative (j) : 0 < Hnative j := hH₀ (Sum.inr j)
  have hdenseNative (j : Tuple) :
      Real.exp (-(pDetect + 1)) * L j ≤
        ((integerProgressionSupport
          (c₀ (Sum.inr (Sigma.mk j.1.val j.2))) (step₀ : ℤ)
          (H₀ (Sum.inr (Sigma.mk j.1.val j.2)))).card : ℝ) := by
    rw [card_integerProgressionSupport _ _ _ hstep₀]
    exact hdenseAll (Sum.inr (Sigma.mk j.1.val j.2))
  have hperiodBounds := canonicalPeriod_primitive_bounds
    (LayerSamplerAxis I n) n selectedRows Q hMkPk hperiodBound
  have hmask := hperiodBounds.2.1.trans (Real.exp_le_exp.mpr hmaskLog)
  have hlabels := hperiodBounds.2.2.trans (Real.exp_le_exp.mpr hlabelLog)
  have hpbase := hperiodBounds.1.trans (Real.exp_le_exp.mpr hperiodLog)
  obtain ⟨hQTg, hPg, hcP, hsP, hstrideGrid⟩ :=
    hgrid stride hMkPk hperiodPos hperiodBound hstridepos hstrideBound
  have hstrideGrid' (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
      ((stepnative j * modulus : ℕ) : ℝ) ≤ Real.exp pg := by
    exact hstrideGrid (Y := PrincipalTupleIndex B (layerSamplerDegree I n))
      stepnative (fun _ => hstepBound) j
  have hnative := exists_allocatedCanonicalSlice_spatial_native_source_sharedWidth
    (s := s) (nX := nX) (ξn := ξn) (τ := τ) (Pphysical := Pphysical) (gain := (allocatedDetectedGain s (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) / 2) (Pproj := Pproj)
    (coarseTarget := coarseTarget) (Ecoarse := Ecoarse) (pGain := pGain)
    B U basis hR hσ S x hMk selection hgood period stride N rfl modulus rfl
    hP hMkP hRP hRi hσi hcount Q hb o bW Hnative stepnative cnative hHnative hsubset r₀ hcell ν μ μrows
    hdimensions hPk hMkPk hPrho htarget hF hQstride hstride hstrideBound hlength
    ρ t htone hs hρ hρ1 hσsmall (fun _ => hstep₀) hδ hδF hdenseNative
    (by simp only [Fintype.card_fin]; omega) y₀ hy₀
    T hT hsource C hC hchart hbudget hρlog hη0 hηsmall
    siteRadius hrone hsitebudget Cforward hforward K hK hradius
    hPbox hVlog hNlog hMlog hbox hvolume hnormalizer hmask hbaseAmbient hvbase hnbase hmbase
    hsites haxes hlabels hKbase hcoords hcutoff hpbase hrowsAmbient houtputs hheight
    Qgrid hQgrid hδ (fun j => hdenseAll (Sum.inr j)) Tg
    (by simpa only [Fintype.card_fin] using hQTg) (fun _ => hstep₀)
    Ag hAg (Real.exp pg) hPg hcP hsP hstrideGrid'
    hBa hBi hDg hvg hwg htg hpg hcube hdegree hrowsD htail hblocks hRv hRiGrid hδw' hTg hcoeff
    le_rfl haxesGrid hfullAxes hfullOutputs hambientCount hprofileBudget
    hBanalytic hDanalytic hcutoffAnalytic hcoordAnalytic hgridAnalytic
    hPnum hI hn hcoeffEarly hRiEarly hVEarly
  have hnative := hnative (Pnative := Pnative) hξn hξnLe cells poly hp hmem signal hsignal hzero
    (lossTarget := lossTarget) (Psample := Psample) (Rrank := Rrank)
    (Sstride := Sstride) (εsample := εsample) (ηsample := ηsample)
    hstridepos hN hτ hPs hX hframe hSstride hSstrideP hεsample hτP hεsampleP hstrideBoundSample
    hsize hrank hRrank hηsample hamb hAmbientP hjet hηsampleP
    hPphysical hMkPhysical hmGeometry hcoarseTarget0 hDimPhysical hGPhysical hXPhysical
    hprecision hηprecision hεprecision
  have hnative := hnative (Pside := Pside) hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
    hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hstrideGeometry hτGeometry
    hgain hPprojGain hcoarseTarget hEcoarseGain hlossTarget
    Cproj Vproj hcoverAmbient hcoverSample hmassSample hCactual hVactual hσ1 hsmall
    hXmass hframeMass hstrideMass hτMass hsizeMass hRrankMass hambMass hjetMass hvars
    hPproj hmProj hGproj hLproj hperiodP hKproj hWproj hRproj hσproj hcountProj hIproj hnProj hJproj
    hProfileProj hCproj hVproj hXproj hFrameProj hStrideProj hτProj hξProj hSizeProj hRankProj
  exact hnative hProjSide hCapSide hpSide htargetSide hside hCells bases hbases hmass hdetectedTuple

end Erdos3.VectorPolynomial

end

end OAI

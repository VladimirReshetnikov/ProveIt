import OAI.Combinatorics.Progressions.Estimates.PreparedModularWitnessCanonicalGeometry
import OAI.Combinatorics.Progressions.Geometry.AllocatedDetectedSpatialNativeSource
import OAI.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorGeometricBounds

namespace OAI

section

namespace Erdos3
open scoped NNReal

private theorem prepared_jointAffineSourceEnvelope_ge_accuracy {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    E ≤ jointAffineSourceEnvelope D P E F := by
  have hInv : 0 ≤ jointAffineInverseEnvelope D P E F := by
    have := affineInverseAxisEnvelope_nonneg hD hP hE hF
    unfold jointAffineInverseEnvelope
    positivity
  have hDer : 0 ≤ jointAffineDerivativeEnvelope D P := by
    have := affineDerivativeAxisEnvelope_nonneg hD hP
    unfold jointAffineDerivativeEnvelope
    positivity
  have hWeight : 0 ≤ jointAffineWeightEnvelope D P E F := by
    have := affineWeightAxisEnvelope_nonneg hD hP hE hF
    unfold jointAffineWeightEnvelope
    positivity
  have hOut := mul_nonneg hD hD
  have hParam := mul_nonneg hD (affineMinorVariableEnvelope_nonneg hD)
  dsimp only [jointAffineSourceEnvelope]
  linarith

theorem prepared_affineProfileToleranceEnvelope_ge_accuracy (degree : ℕ)
    {D N E F : ℝ} (A T : ℝ≥0)
    (hD : 0 ≤ D) (hN : 0 ≤ N) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    E ≤ affineProfileToleranceEnvelope degree D N (A : ℝ) (T : ℝ) E F := by
  have hC : 0 ≤ affineProfileCoefficientEnvelope D (A : ℝ) (T : ℝ) := by
    unfold affineProfileCoefficientEnvelope
    positivity
  have hInput : E ≤ affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F := by
    exact (by linarith : E ≤ E + D + 4).trans
      (prepared_jointAffineSourceEnvelope_ge_accuracy hD hC (by positivity) hF)
  have hRest : 0 ≤ 3 * N * (degree + 2 : ℕ) +
      (2 * (D + affineProfileCoefficientEnvelope D (A : ℝ) (T : ℝ) + degree * D) + 1) := by
    positivity
  unfold affineProfileToleranceEnvelope
  linarith

namespace VectorPolynomial

theorem allocatedAffineLengthLog_mono_density (m : ℕ)
    {D P Prho Pk target F F' Tmod : ℝ} (hF : F ≤ F') :
    allocatedAffineLengthLog m D P Prho Pk target F Tmod ≤
      allocatedAffineLengthLog m D P Prho Pk target F' Tmod := by
  dsimp only [allocatedAffineLengthLog, progressionSliceLengthLog]
  linarith

theorem allocatedAffineLengthLog_prepared_density (m : ℕ)
    (D P Prho Pk target p Tmod : ℝ) :
    allocatedAffineLengthLog m D P Prho Pk target (p + 1) Tmod ≤
      allocatedAffineLengthLog m D P Prho Pk target (p + 2) Tmod :=
  allocatedAffineLengthLog_mono_density m (by linarith)

theorem prepared_affineProfileToleranceEnvelope_kernel_bound {m : ℕ} (hm : 0 < m)
    {D Pk target p : ℝ} (A T : ℝ≥0)
    (hD : 1 ≤ D) (hk : 0 ≤ Pk) (ht : 0 ≤ target) (hp : 0 ≤ p) :
    Pk ≤ affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (A : ℝ) (T : ℝ) (target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5) (p + 2) := by
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hc : (1 : ℝ) ≤ ((m * 2 ^ (m + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos hm (pow_pos (by decide : 0 < (2 : ℕ)) _))
  have hkC : Pk ≤ (m * 2 ^ (m + 1) : ℕ) * Pk := by
    simpa using mul_le_mul_of_nonneg_right hc hk
  have hCD : (m * 2 ^ (m + 1) : ℕ) * Pk ≤
      D * ((m * 2 ^ (m + 1) : ℕ) * Pk) := by
    simpa using mul_le_mul_of_nonneg_right hD (by positivity :
      0 ≤ ((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk)
  have hE : Pk ≤ target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5 := by
    linarith
  exact hE.trans (prepared_affineProfileToleranceEnvelope_ge_accuracy m A T hD0
    (by positivity) (hk.trans hE) (by positivity))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped Classical

variable {X J : Type} {m s : ℕ} (L : RankPreparationFamily X J m)

theorem preparedCommonSamplerBlock_positive_spectrum (hs : s ≤ m) (j : Fin m)
    (i : Fin (preparedSamplerTransverse L j)) :
    positiveModerateSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) *
        (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤
      Fintype.card (PreparedCommonSamplerBlock L ⟨j, Sum.inr i⟩) := by
  simp only [PreparedCommonSamplerBlock, Fintype.card_fin]
  let rows := boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
  have hmax := preparedCommonBlockCount_spectrum m j ⟨s, by omega⟩
  change max (positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount j.val rows.card ((j.val + 1) * rows.card)) ≤
    preparedCommonBlockCount m j at hmax
  change positiveModerateSpectrumBlockCount j.val rows.card
    ((layerTailDegree m + 1) * rows.card) ≤ preparedCommonBlockCount m j
  refine le_trans ?_ ((le_max_left _ _).trans hmax)
  unfold positiveModerateSpectrumBlockCount
  gcongr
  omega

theorem preparedCommonSamplerBlock_uniform_spectrum (hs : s ≤ m) (j : Fin m)
    (i : Fin (preparedSamplerTransverse L j)) :
    uniformSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤
      Fintype.card (PreparedCommonSamplerBlock L ⟨j, Sum.inr i⟩) := by
  simp only [PreparedCommonSamplerBlock, Fintype.card_fin]
  exact (le_max_right _ _).trans (preparedCommonBlockCount_spectrum m j ⟨s, by omega⟩)

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
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (0 + 1))))
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
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
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (0 + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

structure AllocatedEarlyNativeSourceGeometry
    (Pchart P D target Pk Prho Qstride pDetect : ℝ) (K : ℝ≥0) where
  hP : 0 ≤ P
  hRP : ∀ j, R j ≤ Real.exp P
  hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P
  hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P
  hcount : ∀ j : Fin m, (Fintype.card
    (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P
  hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (0 + 1)) selectedRows D
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
  hT : ∀ j, partitionedIdealRadius (Fin (0 + 1)) m + 1 ≤ T j
  hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin (0 + 1)) *
        ((Fintype.card (Fin (0 + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j
  siteRadius : ℝ≥0
  hrone : 1 ≤ siteRadius
  hradius : ∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)
  hbudgets : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp Pchart) →
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
    (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
    (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (0 + 1))) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)
  hK : ∀ j, (R j)⁻¹ ≤ K

def AllocatedPreparedNativeInterface
    (Pchart P _D target Pk Prho Qstride : ℝ) (K : ℝ≥0) : Prop :=
    ∀ (_hMkP : ((allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp P)
    (_hMkPk : ((allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pk)
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
    (_hsites : (Fintype.card (Finset (Fin (0 + 1))) : ℝ) ≤ baseAmbient)
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
    (_hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (_hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg : ℝ}
    (_hDg : 0 ≤ Dg)
    (_hvg : 0 ≤ vg)
    (_hwg : 0 ≤ wg)
    (_hcube : (Fintype.card (Fin (0 + 1)) : ℝ) ≤ Dg)
    (_hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (_hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card : ℝ) ≤ Dg)
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
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin (0 + 1)))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    ∀ {τ Pphysical : ℝ},
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    let ξn := normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) Pphysical coarseTarget
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
    (Fintype.card (Option (Fin (0 + 1)) × (Fin nX)) : ℝ) ≤ Psample →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{0,0,0} m (0 + 1))
    (∀ i, Real.exp ((Psample + A) ^ A) ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin (0 + 1)) J) : ℝ) ≤ Psample →
    ambientBudget ≤ Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (0 + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    (_hPhysicalNonneg : 0 ≤ Pphysical) → (_hMkPhysicalBound : ((allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pphysical) →
    (_hmPhysicalBound : ((m + 1 : ℕ) : ℝ) ≤ Pphysical) → (_hCoarseNonneg : 0 ≤ coarseTarget) →
    (_hDimPhysicalBound : (((0 + 1) + 1 : ℕ) : ℝ) ≤ Pphysical) →
    (_hGPhysicalBound : (Fintype.card G : ℝ) ≤ Pphysical) →
    (_hXPhysicalBound : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical) →
    lossTarget + coefficientErrorSpatialLog Pphysical + 8 ≤ target →
    ηsample ≤ Real.exp (-target) → εsample ≤ Real.exp (-target) →
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m (0 + 1))
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m (0 + 1))
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin (0 + 1))) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * ((m + 1 : ℕ) * Pk))
    let Cgrid := Classical.choose (exists_preparedModularCanonicalDetector_grid_parameters.{0} m (0 + 1) Ag)
    let Qlog := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
    let tg := ((0 + 1 : ℕ) : ℝ) + Qlog + (pDetect + 1) + 1
    let pg := (Cgrid : ℝ) + (((0 + 1) + 1 : ℕ) : ℝ) * Qlog + (pDetect + 1) + 4
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
    Dg ∈ Set.Icc 0 Pnative → p ∈ Set.Icc 0 Pnative → vg ∈ Set.Icc 0 Pnative →
    Fmodel ∈ Set.Icc 0 Pnative → Prho ∈ Set.Icc 0 Pnative → Pk ∈ Set.Icc 0 Pnative →
    target ∈ Set.Icc 0 Pnative → Banalytic ∈ Set.Icc 0 Pnative →
    Pphysical ∈ Set.Icc 0 Pnative → Ecoarse ∈ Set.Icc 0 Pnative → pGain ∈ Set.Icc 0 Pnative →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pphysical) →
    1 / τ ≤ Real.exp Pphysical →
    Real.exp (-pGain) / 2 ≤ (allocatedDetectedZeroGain (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) / 2 →
    pGain + 32 ≤ Pproj → pGain + 32 ≤ coarseTarget →
    pGain + 32 ≤ Ecoarse → pGain + 32 ≤ lossTarget →
    ∀ (Cproj Vproj : Fin m → ℝ≥0),
    let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (0 + 1))
    let coverLog := (Pproj + ((0 + 1) + 2 : ℕ) + Acover) ^ Acover
    let Asample := Classical.choose (exists_allocatedCanonicalProjection_composed_budget m (0 + 1) Acover)
    let Pmass := (Pproj + Asample) ^ Asample
    coverLog ≤ baseAmbient → coverLog ≤ Psample → Pmass ≤ Psample →
    (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ Cproj j * ‖z‖) →
    (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vproj j) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pmass →
    (Fintype.card (Option (Fin (0 + 1)) × Fin nX) : ℝ) ≤ Pmass →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pmass) → 1 / τ ≤ Real.exp Pmass →
    let AmassWindow := Classical.choose (exists_translated_physical_jet_density_window_mass.{0,0,0,max 0 0 0} m (0 + 1))
    (∀ i, Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ (N i : ℝ)) →
    Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ Rrank →
    (Fintype.card (CoefficientAmbientIndex (Fin (0 + 1)) J) : ℝ) ≤ Pmass →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (0 + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Pmass →
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
      (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (0 + 1)))
    (∀ i, Real.exp ((Pproj + Aproj) ^ Aproj) ≤ (N i : ℝ)) →
    Real.exp ((Pproj + Aproj) ^ Aproj) ≤ Rrank →
    ∀ {Pside : ℝ}, Pproj ≤ Pside → Pmass ≤ Pside →
    Pphysical ≤ Pside → coarseTarget ≤ Pside →
    (∀ i, Real.exp ((Pside + Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{0,0,0,0} m)) ^
      Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{0,0,0,0} m)) ≤ (N i : ℝ)) →
    cells.Nonempty → ∀ (bases : Finset (Fin nX → ℤ)), (hbases : bases.Nonempty) →
    let hξn := normalizedTupleNarrowWidth_pos (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) Pphysical coarseTarget
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
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) 0 (dims z j))
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
    (0 + 1) * (0 + 3) ≤ Fintype.card G → (allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) ≤ S.value →
    let C := Classical.choose (exists_canonicalSlicedNative_input_budget m (0 + 1) Amass Aanalytic)
    let Bbudget := (Pnative + C) ^ C
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{0,0,0,0,0,0} m (0 + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} 0)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) 0 budget
          (fun u : integerBox N => u.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => signal u.val) (fun u => star (twistData.eval N poly u.val) * Fnative u)‖

include hb o bW μ ν μrows hR hσ in

theorem allocatedPreparedNativeInterface_of_geometry
    (Pchart D target Pk Prho Qstride : ℝ) (K : ℝ≥0)
    (geometry : AllocatedEarlyNativeSourceGeometry (B := B) (U := U) (basis := basis)
      (S := S) (nX := nX) Pchart P D target Pk Prho Qstride pDetect K) :
    AllocatedPreparedNativeInterface (B := B) (U := U) (basis := basis)
      (hR := hR) (hσ := hσ) (S := S) (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (pDetect := pDetect) (qDetect := qDetect) (α := α)
      (Q := Q) (hb := hb) (o := o) Pchart P D target Pk Prho Qstride K := by
  unfold AllocatedPreparedNativeInterface
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
  have hnative := exists_allocatedDetected_spatial_native_source_zero
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

theorem allocatedPreparedNativeInterface_of_nonempty_geometry
    (Pchart D target Pk Prho Qstride : ℝ) (K : ℝ≥0)
    (geometry : Nonempty (AllocatedEarlyNativeSourceGeometry (B := B) (U := U) (basis := basis)
      (S := S) (nX := nX) Pchart P D target Pk Prho Qstride pDetect K)) :
    AllocatedPreparedNativeInterface (B := B) (U := U) (basis := basis)
      (hR := hR) (hσ := hσ) (S := S) (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (pDetect := pDetect) (qDetect := qDetect) (α := α)
      (Q := Q) (hb := hb) (o := o) Pchart P D target Pk Prho Qstride K := by
  obtain ⟨geometry⟩ := geometry
  exact allocatedPreparedNativeInterface_of_geometry
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

theorem exists_detected_canonical_native_source (m Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)],
      ∀ {P pnum pSlice u Qstride Eextra : ℝ} {nX : ℕ},
      0 < m → 0 ≤ P → 0 ≤ Eextra → pnum ∈ Set.Icc 0 P →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum →
      (∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) → (∀ j, (n j : ℝ) ≤ pnum) →
      (∀ b : LayerSamplerAxis I n, (boundedBooleanJetRows (Fin (0 + 1)) (b.1.val + 1)).card ≤
        Fintype.card (B b)) →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := P + (2 * P + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let _T := allocatedIdealCoverSupport (G := G) B rowSets
      let _siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let target := gainLog + 32 + Eextra
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
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
      let budget := (P + Eextra + C) ^ C
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
        pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ budget ∧
        (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
        pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
        gainLog ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧
        ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
          (U : ∀ j, Submodule ℝ (J j → ℝ))
          (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
          let Pscale := pRadius + Ptail
          ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
            Pscale ∈ Set.Icc 0 budget ∧ Pk ≤ Pscale ∧ (S.value : ℝ) ≤ Real.exp budget ∧
            Nonempty (AllocatedEarlyNativeSourceGeometry (B := B) (U := U) (basis := basis) (S := S) (nX := nX)
              P Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))) ∧
            ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
              Real.exp (-gainLog) ≤
                (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
              (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
              scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value := by
  obtain ⟨C, hC, hgeometry⟩ :=
    exists_detected_canonical_native_source_geometry.{0,0,0,0,0} m 0 Cdetect
  refine ⟨C, hC, ?_⟩
  intro G _ _ I _ n B _ P pnum pSlice u Qstride Eextra nX hm hP hExtra hnum
    hvars hI hn hblocks hpSlice hu hQstride hnX A Pearly rowSets T siteRadius
    pModel pDetect aDetect D gainLog target Pk F Tmod δ E η Prho Ptail K budget
  obtain ⟨pRadius, R, hpRadius, hpRadBudget, hR, hrone, hT0, hTideal,
      hTsource, hTradius, hTbound, hrbound, hTbudget, hrbudget, hsmall,
      hdimensions, hPEarly, hEarlyBudget,
      hpModel, hpDetect, haDetect, htarget, hD, hgain, hPk, hPrho,
      hPtail, hTmod, ρ, hρ, t, ht, htone, htinv, htbudget, hcomparison,
      hsampler⟩ := hgeometry B hm (Nat.zero_le m) hP hExtra hnum
        hvars hI hn hblocks hpSlice hu hQstride hnX
  refine ⟨pRadius, R, hpRadius, hpRadBudget, hR, hpModel, hpDetect,
    hgain, htarget, t, ht, htone, ?_⟩
  intro J _ U basis Pscale
  obtain ⟨hPscale, hScaleLog, S, hRinv, htinv', hcount, hlength, hS, hcutoff⟩ :=
    hsampler U basis
  have hD1 : 1 ≤ D := by
    have hdim := (allocatedComparisonDimension_bounds m hnum.1).2.1
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
    exact hm1.trans hdim
  have hkTail : Pk ≤ Ptail :=
    prepared_affineProfileToleranceEnvelope_kernel_bound hm
      canonicalSublevelCutoffLip canonicalTransitionLip hD1 hPk.1 htarget.1 hpDetect.1
  have hkScale : Pk ≤ Pscale := hkTail.trans (le_add_of_nonneg_left hpRadius.1)
  refine ⟨S, hPscale, hkScale, hS, ?_, ?_⟩
  · refine ⟨{
      hP := hPscale.1
      hRP := fun j => (hR j).2.1.trans (Real.one_le_exp hPscale.1)
      hRi := hRinv
      hσi := htinv'
      hcount := hcount
      hdimensions := hdimensions
      hPk := hPk.1
      hPrho := hPrho.1
      htarget := htarget.1
      hlength := ?_
      η := η
      hη0 := (Real.exp_pos _).le
      hηsmall := ?_
      ρ := ρ
      t := t
      htone := htone
      hs := hcomparison
      hρ := fun partition => (hρ partition).1
      hρ1 := fun partition => (hρ partition).2.1
      hρlog := fun partition => (hρ partition).2.2.1
      hσsmall := fun _ => le_rfl
      T := T
      hT := hTideal
      hsource := hTsource
      siteRadius := siteRadius
      hrone := hrone
      hradius := hTradius
      hbudgets := hsmall
      hK := ?_ }⟩
    · simp only [Fintype.card_fin]
      exact (Real.exp_le_exp.mpr (allocatedAffineLengthLog_prepared_density
        m D Pscale Prho Pk target pDetect Tmod)).trans hlength
    · change Real.exp (-E) ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4))
      apply Real.exp_le_exp.mpr
      dsimp only [E]
      linarith
    · intro j
      simpa only [Real.coe_toNNReal (Real.exp pRadius) (Real.exp_pos _).le] using (hR j).2.2
  · intro α hα
    exact ⟨slicedDetectionGain_lower 0 Cdetect _ hα,
      slicedDetection_kernel_cutoff_bound 0 Cdetect _ G hpDetect.1 hpDetect.1 haDetect.1 hα,
      hcutoff α hα⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def preparedModularCanonicalDetectorConstants (m : ℕ) :
    PreparedModularCanonicalDetectorResourceConstants :=
  let Cgrid := Classical.choose (exists_preparedModularCanonicalDetector_grid_parameters.{0} m 1 canonicalTransitionLip)
  let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m 1)
  let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m 1)
  let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m 1)
  let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{0,0,0,0,0,0} m 1)
  let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} 0)
  { m := m
    Cgrid := Cgrid
    Cperiod := Classical.choose (exists_preparedModularCanonicalDetector_period_budget.{0,0} m 1 Cgrid)
    Acover := Acover
    Asample := Classical.choose (exists_allocatedCanonicalProjection_composed_budget m 1 Acover)
    Cpref := Classical.choose (exists_canonicalSlicedModelPrefactor_budget.{0,0} m 1)
    Apert := Classical.choose (exists_translated_physical_jet_l1_perturbation.{0,0,0} m 1)
    AmassWindow := Classical.choose (exists_translated_physical_jet_density_window_mass.{0,0,0,0} m 1)
    Aproj := Classical.choose (Classical.choose_spec (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m 1))
    Aside := Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{0,0,0,0} m)
    Cnative := Classical.choose (exists_canonicalSlicedNative_input_budget m 1 Amass Aanalytic)
    Anorm := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    Amarginal := Classical.choose (exists_allocated_fullBox_normalized_approximation.{0,0,0,0,0,0} m) }

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type} [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

include U b o hb bW

theorem preparedModularDetector_period_prefactor {P D Pk Qstride pDetect Pnum : ℝ} {nX : ℕ}
    (hP : 0 ≤ P)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1)
      (fun j : Fin m => (boundedBooleanJetRows (Fin 1) (j.val + 1) : Type)) D)
    (hDP : D ≤ P) (hnX : (nX : ℝ) ≤ P) (hPk : Pk ∈ Set.Icc 0 P)
    (hQstride : Qstride ∈ Set.Icc 0 P) (hp : pDetect ∈ Set.Icc 0 P)
    (hPnum : Pnum ∈ Set.Icc 0 P) :
    let r := preparedModularCanonicalDetectorResources (preparedModularCanonicalDetectorConstants m) P
    let O := fun j : Fin m => (boundedBooleanJetRows (Fin 1) (j.val + 1) : Type)
    let L := ((m + 1 : ℕ) : ℝ) * Pk
    let qlog := L + nX * Qstride
    let maskLog := (Fintype.card (LayerSamplerAxis I n) : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)
    let labelLog := (∑ j, (n j : ℝ) * L) + ∑ j, (Fintype.card (Q j) : ℝ) * L
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin 1)) * (Pnum + 8) * (1 + 4 * Pnum) + maskLog
    P ≤ r.Q ∧ L ∈ Set.Icc 0 r.Q ∧ qlog ∈ Set.Icc 0 r.Q ∧
      maskLog ∈ Set.Icc 0 r.Q ∧ labelLog ∈ Set.Icc 0 r.Q ∧ Fmodel ∈ Set.Icc 0 r.Fpref := by
  intro r O L qlog maskLog labelLog Fmodel
  have hQ (j : Fin m) : (Fintype.card (Q j) : ℝ) ≤ P :=
    ((allocatedProfile_dimensions U b o B hdim hb bW).2 j).trans hDP
  have hn := (preparedModularDetector_layer_axes B
    (fun j : Fin m => boundedBooleanJetRows (Fin 1) (j.val + 1)) hdim).2
  have haxes := hdim.axes.trans hDP
  let Cgrid := (preparedModularCanonicalDetectorConstants m).Cgrid
  obtain ⟨hPQ, hL, hq, _, hmask, hlabel, _⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetector_period_budget.{0,0} m 1 Cgrid)).2
      (A := LayerSamplerAxis I n) (nX := nX) n Q hP hnX hPk hQstride hp haxes (fun j => (hn j).trans hDP) hQ
  have hF := (Classical.choose_spec (exists_canonicalSlicedModelPrefactor_budget.{0,0} m 1)).2
    (I := I) (n := n) (Q := Q) hP hPnum hPk haxes hQ
  refine ⟨hPQ, hL, hq, hmask, hlabel, ?_⟩
  change 0 ≤ Fmodel ∧ Fmodel ≤ _
  have heq : Fmodel = (m * (2 : ℝ) ^ Fintype.card (Fin 1)) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L) := by
    dsimp only [Fmodel, maskLog]
    ring
  rw [heq]
  exact hF

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_prepared_detected_canonical_native_source (m Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      let pnum : ℝ := preparedCommonSamplerDimension m M
      ∀ {P pSlice u Qstride Eextra : ℝ} {nX : ℕ},
      0 < m → 0 ≤ P → 0 ≤ Eextra → pnum ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let G := PreparedCommonKernel m
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := PreparedCommonSamplerBlock L
      let _selection := preparedCommonCanonicalSelection m 0 (Nat.zero_le m)
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := P + (2 * P + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let _T := allocatedIdealCoverSupport (G := G) B rowSets
      let _siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let target := gainLog + 32 + Eextra
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
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
      let budget := (P + Eextra + C) ^ C
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
        pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ budget ∧
        (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
        pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
        gainLog ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧
        ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
          (U : ∀ j, Submodule ℝ (J j → ℝ))
          (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
          let Pscale := pRadius + Ptail
          ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
            Pscale ∈ Set.Icc 0 budget ∧ Pk ≤ Pscale ∧ (S.value : ℝ) ≤ Real.exp budget ∧
            Nonempty (AllocatedEarlyNativeSourceGeometry (B := B) (U := U) (basis := basis) (S := S) (nX := nX)
              P Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))) ∧
            ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
              Real.exp (-gainLog) ≤
                (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
              (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
              scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value := by
  obtain ⟨C, hC, hsource⟩ := exists_detected_canonical_native_source m Cdetect
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M hM pnum P pSlice u Qstride Eextra nX hm hP hExtra hnum
    hpSlice hu hQstride hnX G I n B selection A Pearly rowSets T siteRadius
    pModel pDetect aDetect D gainLog target Pk F Tmod δ E η Prho Ptail K budget
  obtain ⟨hvars, hI, hn⟩ := preparedCommonSampler_dimensions L hM
  have hblocks (a : LayerSamplerAxis I n) :
      (boundedBooleanJetRows (Fin (0 + 1)) (a.1.val + 1)).card ≤ Fintype.card (B a) := by
    calc
      _ = Fintype.card (BoundedBooleanJet (Fin (0 + 1)) (a.1.val + 1)) :=
        (Fintype.card_coe _).symm.trans (Fintype.card_congr (boundedBooleanJetRowsEquiv _ _))
      _ ≤ _ := by
        simpa only [B, PreparedCommonSamplerBlock, Fintype.card_fin] using
          preparedCommonBlockCount_jets m a.1 ⟨0, Nat.succ_pos m⟩
  exact hsource (G := G) B hm hP hExtra
    ⟨Nat.cast_nonneg _, hnum⟩ (Nat.cast_le.mpr hvars)
    (fun j => Nat.cast_le.mpr (hI j)) (fun j => Nat.cast_le.mpr (hn j))
    hblocks hpSlice hu hQstride hnX

end Erdos3.VectorPolynomial

end

end OAI

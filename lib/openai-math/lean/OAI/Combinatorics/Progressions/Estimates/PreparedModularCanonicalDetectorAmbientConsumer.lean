import OAI.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorFullBoxConsumer
import OAI.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorGeometricBoundsGeneral

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

theorem preparedModularDetector_scalar_resource_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) {P : ℝ} (hP : 0 ≤ P) :
    let r := preparedModularCanonicalDetectorResources K P
    0 ≤ r.v ∧ 0 ≤ r.w ∧ 0 ≤ r.Dg ∧ 0 ≤ r.Pbox ∧
      0 ≤ r.Vlog ∧ 0 ≤ r.Nlog ∧ 0 ≤ r.Banalytic ∧ 0 ≤ r.baseAmbient ∧
      P ≤ r.v ∧ P + 1 ≤ r.w ∧ 2 * P ≤ r.Dg ∧ K.m * P ≤ r.Dg ∧
      ((layerTailDegree K.m + 1 : ℕ) : ℝ) ≤ r.Dg ∧ 1 ≤ r.Dg ∧
      r.Dg ≤ r.Banalytic ∧ 4 * P ≤ r.Banalytic ∧ P + 8 ≤ r.Banalytic ∧
      P ≤ r.baseAmbient ∧ 3 * P ≤ r.baseAmbient ∧ 2 * P ≤ r.baseAmbient ∧
      r.Vlog ≤ r.baseAmbient ∧ r.Nlog ≤ r.baseAmbient ∧
      ((layerTailDegree K.m + 1 : ℕ) : ℝ) * P ≤ r.baseAmbient ∧ 2 ≤ r.baseAmbient := by
  intro r
  have hdeg : 0 ≤ ((layerTailDegree K.m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ K.m := Nat.cast_nonneg _
  have hprof : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
  have hmP : (0 : ℝ) ≤ K.m * P := mul_nonneg hm hP
  have hdegP : 0 ≤ ((layerTailDegree K.m + 1 : ℕ) : ℝ) * P := mul_nonneg hdeg hP
  have hv : r.v = P + 8 := rfl
  have hw : r.w = P + 1 := rfl
  have hbox : r.Pbox = 2 * P + 8 := rfl
  have hd : r.Dg = 2 * P + K.m * P + (layerTailDegree K.m + 1 : ℕ) +
      K.m + comparisonProfileBound + 8 := rfl
  have hba : r.Banalytic = r.Dg + 4 * P + 32 := rfl
  have ha : r.baseAmbient = r.Pproj + r.coverLog + r.Vlog + r.Nlog + r.Q +
      (layerTailDegree K.m + 1 : ℕ) * P + 3 * P + comparisonProfileBound + 32 := rfl
  have hproj : 0 ≤ r.Pproj := by change 0 ≤ 4 * (P + 8)^2; positivity
  have hcover : 0 ≤ r.coverLog := by
    change 0 ≤ (r.Pproj + 3 + K.Acover)^K.Acover
    positivity
  have hq : 0 ≤ r.Q := by change 0 ≤ (P + K.Cperiod)^K.Cperiod; positivity
  have hvl : 0 ≤ r.Vlog := by
    change 0 ≤ P^2 * ((layerTailDegree K.m + 1 : ℕ) * P + 1)
    positivity
  have hnl : 0 ≤ r.Nlog := by
    change 0 ≤ (2 * K.m : ℕ) * (2 * P + 16) * (1 + 4 * (2 * P + 8))
    positivity
  have hd0 : 0 ≤ r.Dg := by linarith only [hd, hP, hmP, hdeg, hm, hprof]
  have hba0 : 0 ≤ r.Banalytic := by linarith only [hba, hd0, hP]
  have ha0 : 0 ≤ r.baseAmbient := by
    linarith only [ha, hproj, hcover, hvl, hnl, hq, hdegP, hP, hprof]
  refine ⟨by linarith only [hv, hP], by linarith only [hw, hP], hd0,
    by linarith only [hbox, hP], hvl, hnl, hba0, ha0, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hv]
  · exact hw.ge
  · linarith only [hd, hmP, hdeg, hm, hprof]
  · linarith only [hd, hP, hdeg, hm, hprof]
  · linarith only [hd, hP, hmP, hm, hprof]
  · linarith only [hd, hP, hmP, hdeg, hm, hprof]
  · linarith only [hba, hP]
  · linarith only [hba, hd0]
  · linarith only [hba, hd0, hP]
  all_goals linarith only [ha, hproj, hcover, hvl, hnl, hq, hdegP, hP, hprof]

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin 1)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

structure PreparedModularDetectorAmbientBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) (P D pDetect : ℝ) : Prop where
  hPbox : 0 ≤ r.Pbox
  hVlog : 0 ≤ r.Vlog
  hNlog : 0 ≤ r.Nlog
  hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp r.Pbox
  hvolume : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp r.Vlog
  hnormalizer : ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp r.Nlog
  sourceNumerics : AllocatedSourceNumerics B U b S C V r.Pbox
  hbaseAmbient : 0 ≤ r.baseAmbient
  hvbase : r.Vlog ≤ r.baseAmbient
  hnbase : r.Nlog ≤ r.baseAmbient
  hsites : (Fintype.card (Finset (Fin 1)) : ℝ) ≤ r.baseAmbient
  haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ r.baseAmbient
  hKbase : (Ksource : ℝ) ≤ Real.exp r.baseAmbient
  hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp r.baseAmbient
  hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp r.baseAmbient
  hrowsAmbient : ((∑ j, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.baseAmbient
  houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ r.baseAmbient
  hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp r.baseAmbient
  hQgrid : ∀ a : {a // grid a},
    8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤
        (Real.toNNReal (8 * (D + 1)) : ℝ)
  hDg : 0 ≤ r.Dg
  hvg : 0 ≤ r.v
  hwg : 0 ≤ r.w
  hcube : (Fintype.card (Fin 1) : ℝ) ≤ r.Dg
  hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ r.Dg
  hrowsD : ∀ j, ((rowSets j).card : ℝ) ≤ r.Dg
  htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ r.Dg
  hblocks : ∀ a, (Fintype.card (B a) : ℝ) ≤ r.Dg
  hRv : ∀ j, R j ≤ Real.exp r.v
  hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp r.v
  hδw : pDetect + 1 ≤ r.w
  hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp r.v
  haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ r.Dg
  hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ r.Dg
  hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ r.Dg
  hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ r.Dg
  hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ r.Dg
  hBanalytic : 0 ≤ r.Banalytic
  hDanalytic : r.Dg ≤ r.Banalytic
  hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp r.Banalytic
  hcoordAnalytic : ((Ksource * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤
    Real.exp r.Banalytic
  hgridAnalytic : (Real.toNNReal (8 * (D + 1)) : ℝ) ≤ Real.exp r.Banalytic
  hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P
  hn : ∀ j, (n j : ℝ) ≤ P
  hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P
  hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp P
  hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P

private theorem row_count_exp {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1) rowTypes D) (hDP : D ≤ P) :
    ((∑ j, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp (2 * P) := by
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  have hPexp : P ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  have hmexp : (m : ℝ) ≤ Real.exp P := hdim.degree.trans (hDP.trans hPexp)
  push_cast
  calc
    _ ≤ ∑ _j : Fin m, P := by
      apply Finset.sum_le_sum
      intro j _
      have h := (hdim.rows j).trans hDP
      simpa only [Fintype.card_coe] using h
    _ = (m : ℝ) * P := by simp
    _ ≤ Real.exp P * Real.exp P := mul_le_mul hmexp hPexp hP (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem preparedModularDetector_ambient_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (hm : K.m = m) {P D pDetect : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1) rowTypes D) (hDP : D ≤ P)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hS : (S.value : ℝ) ≤ Real.exp P) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp P) (hV : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hvolumeRatio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hforward : ∀ j, (Cforward j : ℝ) ≤ Real.exp P) (hK : (Ksource : ℝ) ≤ Real.exp P)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp P) (hDetect : pDetect ≤ P) :
    PreparedModularDetectorAmbientBounds B rowSets U b S C V Cforward Ksource
      (preparedModularCanonicalDetectorResources K P) P D pDetect := by
  let r := preparedModularCanonicalDetectorResources K P
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  obtain ⟨hv0, hw0, hdg0, hbox0, hvol0, hnorm0, hba0, hbase0,
    hPv, hPw, h2PDg, hmPDg, htailDg, h1Dg, hDgBa, h4PBa, h8PBa,
    hPBase, h3PBase, h2PBase, hVBase, hNBase, htailBase, h2Base⟩ :=
      preparedModularDetector_scalar_resource_bounds K hP
  change 0 ≤ r.v at hv0
  have hPDg : P ≤ r.Dg := (by linarith : P ≤ 2 * P).trans h2PDg
  have hDDg : D ≤ r.Dg := hDP.trans hPDg
  have hPBa : P ≤ r.Banalytic := (by linarith : P ≤ 4 * P).trans h4PBa
  have hPexp : P ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  have hExpv : Real.exp P ≤ Real.exp r.v := Real.exp_le_exp.mpr hPv
  have hExpBase : Real.exp P ≤ Real.exp r.baseAmbient := Real.exp_le_exp.mpr hPBase
  have hExpBa : Real.exp P ≤ Real.exp r.Banalytic := Real.exp_le_exp.mpr hPBa
  have hSource := preparedModularDetector_source_numerics B rowSets U b S C V
    hdim hDP hRi hσi hS hJ hC hV
  have hBox := preparedModularDetector_site_radius B rowSets hdim hDP
  have hVol : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp r.Vlog := by
    simpa only [r, preparedModularCanonicalDetectorResources, hm] using
      preparedModularDetector_natural_volume B rowSets U b S hP hdim hDP hR hRone hS
  have hNlog : r.Nlog = ((m : ℝ) * 2) * (2 * P + 16) * (1 + 4 * (2 * P + 8)) := by
    dsimp only [r, preparedModularCanonicalDetectorResources]
    rw [hm]
    push_cast
    ring
  have hNorm : ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      Real.exp r.Nlog := by
    rw [hNlog]
    exact preparedModularDetector_inverse_normalizer B rowSets U b S C V
      hdim hDP hR hRi hσi hS hJ hC hV hvolumeRatio
  obtain ⟨hSlots, hSlotsExp⟩ := preparedModularDetector_grid_slot_cap B rowSets U b S hdim hDP
  obtain ⟨hI, hn⟩ := preparedModularDetector_layer_axes B rowSets hdim
  have hCoords := preparedModularDetector_chart_sum B rowSets Cforward hdim hDP hJ hforward
  have hCoordAnalytic : ((Ksource * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤
      Real.exp r.Banalytic := by
    rw [NNReal.coe_mul]
    calc
      _ ≤ Real.exp P * Real.exp (3 * P) :=
        mul_le_mul hK hCoords (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (4 * P) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr h4PBa
  have hHeight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp r.baseAmbient := by
    have htail : ((layerTailDegree m + 1 : ℕ) : ℝ) * P ≤ r.baseAmbient := by
      simpa only [hm] using htailBase
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hS _).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr htail
  refine {
    hPbox := hbox0
    hVlog := hvol0
    hNlog := hnorm0
    hbox := hBox
    hvolume := hVol
    hnormalizer := hNorm
    sourceNumerics := hSource
    hbaseAmbient := hbase0
    hvbase := hVBase
    hnbase := hNBase
    hsites := ?_
    haxes := hdim.axes.trans (hDP.trans hPBase)
    hKbase := hK.trans hExpBase
    hcoords := hCoords.trans (Real.exp_le_exp.mpr h3PBase)
    hcutoff := hcutoff.trans hExpBase
    hrowsAmbient := (row_count_exp B rowSets hdim hDP).trans (Real.exp_le_exp.mpr h2PBase)
    houtputs := hdim.outputs.trans (hDP.trans hPBase)
    hheight := hHeight
    hQgrid := hSlots
    hDg := hdg0
    hvg := hv0
    hwg := hw0
    hcube := ?_
    hdegree := fun j => (hdim.layer_degree B j).trans hDDg
    hrowsD := ?_
    htail := ?_
    hblocks := fun a => (preparedModularDetector_blocks B rowSets hdim a).trans (by linarith)
    hRv := fun j => (hRone j).trans (Real.one_le_exp hv0)
    hRiGrid := fun j => (hRi j).trans hExpv
    hδw := by linarith only [hDetect, hPw]
    hcoeff := fun j => (hdim.coefficients j).trans (hDP.trans (hPexp.trans hExpv))
    haxesGrid := (preparedModularDetector_grid_axes B rowSets U b S hdim).trans hDDg
    hfullAxes := hdim.axes.trans hDDg
    hfullOutputs := hdim.outputs.trans hDDg
    hambientCount := ?_
    hprofileBudget := hdim.profile.trans hDDg
    hBanalytic := hba0
    hDanalytic := hDgBa
    hcutoffAnalytic := hcutoff.trans hExpBa
    hcoordAnalytic := hCoordAnalytic
    hgridAnalytic := hSlotsExp.trans (Real.exp_le_exp.mpr h8PBa)
    hI := fun j => (hI j).trans hDP
    hn := fun j => (hn j).trans hDP
    hcoeffEarly := fun j => (hdim.coefficients j).trans hDP
    hRiEarly := hRi
    hVEarly := fun j => (hvolumeRatio j).trans (hV j) }
  · simpa only [Fintype.card_finset, Fintype.card_fin, pow_one, Nat.cast_ofNat] using h2Base
  · simpa only [Fintype.card_fin, Nat.cast_one] using h1Dg
  · intro j
    simpa only [Fintype.card_coe] using (hdim.rows j).trans hDDg
  · simpa only [hm] using htailDg
  · apply (preparedModularDetector_ambient_count hJ).trans
    simpa only [hm] using hmPDg

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

structure PreparedModularGeneralEarlyAnalyticBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) (P D pDetect : ℝ) : Prop where
  hQgrid : ∀ a : {a // grid a},
    8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤
        (Real.toNNReal (8 * (D + 1)) : ℝ)
  hDg : 0 ≤ r.Dg
  hvg : 0 ≤ r.v
  hwg : 0 ≤ r.w
  hcube : (Fintype.card (Fin dim) : ℝ) ≤ r.Dg
  hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ r.Dg
  hrowsD : ∀ j, ((rowSets j).card : ℝ) ≤ r.Dg
  htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ r.Dg
  hblocks : ∀ a, (Fintype.card (B a) : ℝ) ≤ r.Dg
  hRv : ∀ j, R j ≤ Real.exp r.v
  hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp r.v
  hδw : pDetect + 1 ≤ r.w
  hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp r.v
  haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ r.Dg
  hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ r.Dg
  hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ r.Dg
  hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ r.Dg
  hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ r.Dg
  hBanalytic : 0 ≤ r.Banalytic
  hDanalytic : r.Dg ≤ r.Banalytic
  hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp r.Banalytic
  hcoordAnalytic : ((Ksource * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤
    Real.exp r.Banalytic
  hgridAnalytic : (Real.toNNReal (8 * (D + 1)) : ℝ) ≤ Real.exp r.Banalytic
  hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P
  hn : ∀ j, (n j : ℝ) ≤ P
  hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P
  hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp P
  hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P

theorem preparedModularGeneralDetector_early_analytic_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (hm : K.m = m) {P D pDetect : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) (hDP : D ≤ P)
    (hRone : ∀ j, R j ≤ 1) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hV : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hvolumeRatio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hforward : ∀ j, (Cforward j : ℝ) ≤ Real.exp P) (hK : (Ksource : ℝ) ≤ Real.exp P)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp P) (hDetect : pDetect ≤ P) :
    PreparedModularGeneralEarlyAnalyticBounds B rowSets U b S Cforward Ksource
      (preparedModularCanonicalDetectorResources K P) P D pDetect := by
  let r := preparedModularCanonicalDetectorResources K P
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  obtain ⟨hv0, hw0, hdg0, hbox0, hvol0, hnorm0, hba0, hbase0,
    hPv, hPw, h2PDg, hmPDg, htailDg, h1Dg, hDgBa, h4PBa, h8PBa,
    hPBase, h3PBase, h2PBase, hVBase, hNBase, htailBase, h2Base⟩ :=
      preparedModularDetector_scalar_resource_bounds K hP
  have hPDg : P ≤ r.Dg := (by linarith only [hP] : P ≤ 2 * P).trans h2PDg
  have hDDg : D ≤ r.Dg := hDP.trans hPDg
  have hPexp : P ≤ Real.exp P := by linarith only [Real.add_one_le_exp P]
  have hExpv : Real.exp P ≤ Real.exp r.v := Real.exp_le_exp.mpr hPv
  have hExpBa : Real.exp P ≤ Real.exp r.Banalytic :=
    Real.exp_le_exp.mpr ((by linarith only [hP] : P ≤ 4 * P).trans h4PBa)
  obtain ⟨hSlots, hSlotsExp⟩ := preparedModularGeneralDetector_grid_slot_cap B rowSets U b S hdim hDP
  obtain ⟨hI, hn⟩ := preparedModularGeneralDetector_layer_axes B rowSets hdim
  have hCoords := preparedModularGeneralDetector_chart_sum B rowSets Cforward hdim hDP hJ hforward
  have hCoordAnalytic : ((Ksource * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤
      Real.exp r.Banalytic := by
    rw [NNReal.coe_mul]
    calc
      _ ≤ Real.exp P * Real.exp (3 * P) :=
        mul_le_mul hK hCoords (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (4 * P) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr h4PBa
  refine {
    hQgrid := hSlots
    hDg := hdg0
    hvg := hv0
    hwg := hw0
    hcube := hdim.cube.trans hDDg
    hdegree := fun j => (hdim.layer_degree B j).trans hDDg
    hrowsD := ?_
    htail := ?_
    hblocks := fun a => (preparedModularGeneralDetector_blocks B rowSets hdim a).trans (by linarith only [hDP, h2PDg])
    hRv := fun j => (hRone j).trans (Real.one_le_exp hv0)
    hRiGrid := fun j => (hRi j).trans hExpv
    hδw := by linarith only [hDetect, hPw]
    hcoeff := fun j => (hdim.coefficients j).trans (hDP.trans (hPexp.trans hExpv))
    haxesGrid := (preparedModularGeneralDetector_grid_axes B rowSets U b S hdim).trans hDDg
    hfullAxes := hdim.axes.trans hDDg
    hfullOutputs := hdim.outputs.trans hDDg
    hambientCount := ?_
    hprofileBudget := hdim.profile.trans hDDg
    hBanalytic := hba0
    hDanalytic := hDgBa
    hcutoffAnalytic := hcutoff.trans hExpBa
    hcoordAnalytic := hCoordAnalytic
    hgridAnalytic := hSlotsExp.trans (Real.exp_le_exp.mpr h8PBa)
    hI := fun j => (hI j).trans hDP
    hn := fun j => (hn j).trans hDP
    hcoeffEarly := fun j => (hdim.coefficients j).trans hDP
    hRiEarly := hRi
    hVEarly := fun j => (hvolumeRatio j).trans (hV j) }
  · intro j
    simpa only [Fintype.card_coe] using (hdim.rows j).trans hDDg
  · simpa only [hm] using htailDg
  · apply (preparedModularGeneralDetector_ambient_count hJ).trans
    simpa only [hm] using hmPDg

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem preparedModularGeneralDetector_early_normalizer {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) (hDP : D ≤ P)
    (hR : ∀ j, 0 < R j) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      Real.exp ((m * (2 : ℝ) ^ dim) * (P + 8) * (1 + 4 * P)) := by
  obtain ⟨hI, hn⟩ := preparedModularGeneralDetector_layer_axes B rowSets hdim
  simpa only [Fintype.card_fin] using
    allocatedProductIdealNormalizer_early_budget B U b S rowSets hR (hdim.nonneg.trans hDP)
      (fun j => (hI j).trans hDP) (fun j => (hn j).trans hDP)
      (fun j => (hdim.coefficients j).trans hDP) hRi hV

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

structure PreparedModularGeneralLateAmbientBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) : Prop where
  hPbox : 0 ≤ r.Pbox
  hVlog : 0 ≤ r.Vlog
  hNlog : 0 ≤ r.Nlog
  hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp r.Pbox
  hvolume : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp r.Vlog
  hnormalizer : ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp r.Nlog
  hbaseAmbient : 0 ≤ r.baseAmbient
  hvbase : r.Vlog ≤ r.baseAmbient
  hnbase : r.Nlog ≤ r.baseAmbient
  hsites : (Fintype.card (Finset (Fin dim)) : ℝ) ≤ r.baseAmbient
  haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ r.baseAmbient
  hKbase : (Ksource : ℝ) ≤ Real.exp r.baseAmbient
  hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp r.baseAmbient
  hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp r.baseAmbient
  hrowsAmbient : ((∑ j, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.baseAmbient
  houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ r.baseAmbient
  hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp r.baseAmbient

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem preparedModularGeneralDetector_late_ambient_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (hm : K.m = m) {P L D : ℝ}
    (hPL : P ≤ L)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) (hDP : D ≤ P)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hS : (S.value : ℝ) ≤ Real.exp L)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P)
    (hforward : ∀ j, (Cforward j : ℝ) ≤ Real.exp P) (hK : (Ksource : ℝ) ≤ Real.exp P)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp P) :
    PreparedModularGeneralLateAmbientBounds B rowSets U b S Cforward Ksource
      (preparedModularGeneralDetectorResources K dim P L) := by
  let r := preparedModularGeneralDetectorResources K dim P L
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  have hL : 0 ≤ L := hP.trans hPL
  have hb := ((Classical.choose_spec (exists_preparedModularGeneralDetector_resource_budget K dim)).2 hP hPL).1
  have htail : 0 ≤ ((layerTailDegree K.m + 1 : ℕ) : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL
  have hconst : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
  have hsites0 : (0 : ℝ) ≤ (2 ^ dim : ℕ) := Nat.cast_nonneg _
  have hbase : r.baseAmbient = r.Pproj + r.coverLog + r.Vlog + r.Nlog + r.Q +
      (layerTailDegree K.m + 1 : ℕ) * L + 3 * P + comparisonProfileBound + (2 ^ dim : ℕ) + 32 := rfl
  have hPbase : P ≤ r.baseAmbient := by
    linarith only [hbase, hb.Pproj.1, hb.coverLog.1, hb.Vlog.1, hb.Nlog.1, hb.Q.1, htail, hP, hconst, hsites0]
  have h3Pbase : 3 * P ≤ r.baseAmbient := by
    linarith only [hbase, hb.Pproj.1, hb.coverLog.1, hb.Vlog.1, hb.Nlog.1, hb.Q.1, htail, hconst, hsites0]
  have h2Pbase : 2 * P ≤ r.baseAmbient := (by linarith only [hP] : 2 * P ≤ 3 * P).trans h3Pbase
  have hvol : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp r.Vlog := by
    simpa only [r, preparedModularGeneralDetectorResources, hm] using
      preparedModularGeneralDetector_natural_volume B rowSets U b S hL hdim (hDP.trans hPL) hR hRone hS
  have hnorm : ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp r.Nlog := by
    simpa only [r, preparedModularGeneralDetectorResources, hm, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      preparedModularGeneralDetector_early_normalizer B rowSets U b S hdim hDP hR hRi hV
  have hrows : ((∑ j, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp (2 * P) := by
    have hPexp : P ≤ Real.exp P := by linarith only [Real.add_one_le_exp P]
    have hmexp : (m : ℝ) ≤ Real.exp P := hdim.degree.trans (hDP.trans hPexp)
    push_cast
    calc
      _ ≤ ∑ _j : Fin m, P := Finset.sum_le_sum (fun j _ => by
        simpa only [Fintype.card_coe] using (hdim.rows j).trans hDP)
      _ = (m : ℝ) * P := by simp
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hmexp hPexp hP (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp r.baseAmbient := by
    have hlog : ((layerTailDegree m + 1 : ℕ) : ℝ) * L ≤ r.baseAmbient := by
      rw [← hm]
      linarith only [hbase, hb.Pproj.1, hb.coverLog.1, hb.Vlog.1, hb.Nlog.1, hb.Q.1, hP, hconst, hsites0]
    calc
      _ ≤ (Real.exp L) ^ (layerTailDegree m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hS _
      _ = Real.exp (((layerTailDegree m + 1 : ℕ) : ℝ) * L) := by rw [← Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  refine {
    hPbox := hb.Pbox.1
    hVlog := hb.Vlog.1
    hNlog := hb.Nlog.1
    hbox := preparedModularGeneralDetector_site_radius B rowSets hdim hDP
    hvolume := hvol
    hnormalizer := hnorm
    hbaseAmbient := hb.baseAmbient.1
    hvbase := ?_
    hnbase := ?_
    hsites := ?_
    haxes := hdim.axes.trans (hDP.trans hPbase)
    hKbase := hK.trans (Real.exp_le_exp.mpr hPbase)
    hcoords := (preparedModularGeneralDetector_chart_sum B rowSets Cforward hdim hDP hJ hforward).trans (Real.exp_le_exp.mpr h3Pbase)
    hcutoff := hcutoff.trans (Real.exp_le_exp.mpr hPbase)
    hrowsAmbient := hrows.trans (Real.exp_le_exp.mpr h2Pbase)
    houtputs := hdim.outputs.trans (hDP.trans hPbase)
    hheight := hheight }
  · linarith only [hbase, hb.Pproj.1, hb.coverLog.1, hb.Nlog.1, hb.Q.1, htail, hP, hconst, hsites0]
  · linarith only [hbase, hb.Pproj.1, hb.coverLog.1, hb.Vlog.1, hb.Q.1, htail, hP, hconst, hsites0]
  · simp only [Fintype.card_finset, Fintype.card_fin]
    linarith only [hbase, hb.Pproj.1, hb.coverLog.1, hb.Vlog.1, hb.Nlog.1, hb.Q.1, htail, hP, hconst]

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
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
local notation "qDetect" => allocatedModelTestLog u pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
local notation "α" => allocatedModelUnitThreshold u pModel Kslice Ctail
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

include hb o bW μ ν μrows hR hσ in

theorem preparedModularCanonicalDetectorAmbientConsumer
    (Pchart D target Pk Prho Qstride : ℝ) (K : ℝ≥0)
    (geometry : AllocatedEarlyNativeSourceGeometry (B := B) (U := U) (basis := basis)
      (S := S) (nX := nX) Pchart P D target Pk Prho Qstride pDetect K)
    {Pmaster : ℝ} (hMaster : 0 ≤ Pmaster) (hDMaster : D ≤ Pmaster)
    (hPkMaster : Pk ∈ Set.Icc 0 Pmaster) (hQstrideMaster : Qstride ∈ Set.Icc 0 Pmaster)
    (hDetectMaster : pDetect ∈ Set.Icc 0 Pmaster) (hnXMaster : (nX : ℝ) ≤ Pmaster)
    (hRone : ∀ j, R j ≤ 1)
    (hRiMaster : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσiMaster : ∀ j, (σ j)⁻¹ ≤ Real.exp Pmaster)
    (hSMaster : (S.value : ℝ) ≤ Real.exp Pmaster)
    (hKMaster : (K : ℝ) ≤ Real.exp Pmaster)
    (hcutoffMaster : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pmaster)
    (hMkP : ((allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp P)
    (hMkPk : ((allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pk)
    (hstride : ∀ i, 0 < stride i) (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (hForwardMaster : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pmaster)
    (hVtailMaster : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pmaster)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩)) :
    let r := preparedModularCanonicalDetectorResources (preparedModularCanonicalDetectorConstants m) Pmaster
    let Pbox := r.Pbox
    let Vlog := r.Vlog
    let Nlog := r.Nlog
    let Mlog := r.Q
    let baseAmbient := r.baseAmbient
    let _Qgrid := Real.toNNReal (8 * (D + 1))
    let Ag := canonicalTransitionLip
    let Dg := r.Dg
    let vg := r.v
    let wg := r.w
    let Banalytic := r.Banalytic
    let Pnum := Pmaster
    ∀ {Pproj coarseTarget Ecoarse pGain : ℝ},
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
,
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
    ∀ (Cproj : Fin m → ℝ≥0),
    let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (0 + 1))
    let coverLog := (Pproj + ((0 + 1) + 2 : ℕ) + Acover) ^ Acover
    let Asample := Classical.choose (exists_allocatedCanonicalProjection_composed_budget m (0 + 1) Acover)
    let Pmass := (Pproj + Asample) ^ Asample
    coverLog ≤ baseAmbient → coverLog ≤ Psample → Pmass ≤ Psample →
    (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ Cproj j * ‖z‖) →
    (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j) →
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
    (∀ j, (Cproj j : ℝ) ≤ Real.exp Pproj) → (∀ j, (Vtail j : ℝ) ≤ Real.exp Pproj) →
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
    cells.Nonempty →
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    ∀ (hbases : bases.Nonempty),
    let hξn := normalizedTupleNarrowWidth_pos (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) Pphysical coarseTarget
    ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z),
    (htotal : 0 < selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)) →
    let Path := bases × rectangularWeightIndices 0 V 1
    let pathLaw := allocatedOriginalPathLaw B U basis hb o hR hσ S (Fin nX) poly hmem N
      (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hW hτSpatial hξn stride cells hmass bases hbases htotal
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let e : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    ∀ {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
      {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)] [∀ z j, LieAlgebra ℚ (Ldetect z j)]
      {dims : ∀ z, Tests z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) 0 (dims z j))
      (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
      (slices : ∀ z, Tests z → Finset Sites)
      (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
      (stepdetect : ∀ z, Tests z → ℕ)
      (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < stepdetect z j) →
    (∀ z j, (slices z j).image e = commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j)) →
    (∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)) pSlice ((slices z j).image e)) →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect →
    (∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect)) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    (0 + 1) * (0 + 3) ≤ Fintype.card G → (allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) ≤ S.value →
    let Cbudget := Classical.choose (exists_canonicalSlicedNative_input_budget m (0 + 1) Amass Aanalytic)
    let Bbudget := (Pnative + Cbudget) ^ Cbudget
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{0,0,0,0,0,0} m (0 + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} 0)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    0 ≤ u → 0 ≤ pModel → 0 ≤ budget →
    pSlice ≤ pModel → pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ pModel →
    Ctail ≤ Real.exp pModel →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp pModel →
    (∀ j, σ j ≤ 1) →
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) →
    τ ≤ 1 / 2 → (Fintype.card (Fin nX) : ℝ) * τ ≤ 1 / 2 → (hξone : ξn ≤ 1) →
    ∀ {Efull : ℝ},
    let Afull := Classical.choose (exists_allocated_fullBox_normalized_approximation.{0,0,0,0,0,0} m)
    (∀ i, Real.exp ((max Pproj Efull + Afull) ^ Afull) ≤ (N i : ℝ)) →
    Real.exp ((max Pproj Efull + Afull) ^ Afull) ≤ Rrank →
    u + 2 * pModel + budget + 30 ≤ Efull →
    ∃ hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i,
    let hrootSum := fun t : Sites => allocatedParameterBox_root_bound B U basis S t
    let physical := narrowPhysicalSiteMap (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτSpatial
      hξone N (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i)))
      hmargin e hrootSum
    ∀ (input : integerBox N → ℂ), (∀ t, ‖input t‖ ≤ Real.exp pModel) →
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (Qmodel : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, Qmodel i ∈ twistedNativeSampleFunctions (fun _ : Fin nX => 1) 0 budget
        (fun t : integerBox N => t.val)
        (fun (twist : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
            (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩)
          (t : integerBox N) => twist.eval N poly t.val)) ∧
      input = (∑ i, coeff i • Qmodel i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (budget + 2) ∧
      sampledSliceSeminorm pathLaw physical slices
        (fun z j t => star ((Vdetect z j).eval
          (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) err ≤ Real.exp (-u) ∧
      (nterms : ℝ) ≤ Real.exp (2 * budget + 2 * u + 4 * pModel + 30) := by
  intro r Pbox Vlog Nlog Mlog baseAmbient Qgrid Ag Dg vg wg Banalytic Pnum
  have hd := geometry.hdimensions
  have hJ := (allocatedProfile_dimensions U basis o B hd hb bW).1
  have ambient := preparedModularDetector_ambient_bounds B rowSets U basis S
    Cforward Vtail Cforward K (preparedModularCanonicalDetectorConstants m) rfl hd hDMaster
    hR hRone hRiMaster hσiMaster hSMaster (fun j => (hJ j).trans hDMaster)
    hForwardMaster hVtailMaster (fun j => (hVactual j).2) hForwardMaster hKMaster hcutoffMaster hDetectMaster.2
  obtain ⟨_, hperiod, _, hmask, hlabel, _⟩ :=
    preparedModularDetector_period_prefactor B U basis o hb bW hMaster hd hDMaster
      hnXMaster hPkMaster hQstrideMaster hDetectMaster ⟨hMaster, le_rfl⟩
  have hQbase : r.Q ≤ r.baseAmbient := by
    have hr := ((Classical.choose_spec (exists_preparedModularCanonicalDetector_resource_budget
      (preparedModularCanonicalDetectorConstants m))).2 Pmaster hMaster).1
    have hm : 0 ≤ ((layerTailDegree m + 1 : ℕ) : ℝ) * Pmaster := mul_nonneg (Nat.cast_nonneg _) hMaster
    change r.Q ≤ r.Pproj + r.coverLog + r.Vlog + r.Nlog + r.Q +
      (layerTailDegree m + 1 : ℕ) * Pmaster + 3 * Pmaster + comparisonProfileBound + 32
    linarith only [hr.Pproj.1, hr.coverLog.1, hr.Vlog.1, hr.Nlog.1, hm, hMaster,
      Nat.cast_nonneg («α» := ℝ) comparisonProfileBound]
  have hNative := allocatedPreparedNativeInterface_of_geometry
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) («pDetect» := pDetect) («qDetect» := qDetect) («α» := α)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
    Pchart D target Pk Prho Qstride K geometry
  intro Pproj coarseTarget Ecoarse pGain ambientQ ambientBudget τ Pphysical
  exact preparedModularCanonicalDetectorFullBoxConsumer
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
    (selection := selection) (stride := stride) (N := N) (Pdetect := Pdetect)
    (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
    (Q := Q) (hb := hb) (o := o) (ν := ν) (μ := μ)
    Pchart D target Pk Prho Qstride K hNative
    hMkP hMkPk hQstrideMaster.1 hstride hstrideBound C hC hCbound hchart Cforward hforward
    ambient.hPbox ambient.hVlog ambient.hNlog (hmask.1.trans hmask.2) ambient.hbox ambient.hvolume
    ambient.hnormalizer hmask.2 ambient.hbaseAmbient ambient.hvbase ambient.hnbase hQbase
    ambient.hsites ambient.haxes (hlabel.2.trans hQbase) ambient.hKbase ambient.hcoords
    ambient.hcutoff (hperiod.2.trans hQbase) ambient.hrowsAmbient ambient.houtputs ambient.hheight
    Qgrid ambient.hQgrid Ag canonicalTransitionLip_spec hBa hBi
    ambient.hDg ambient.hvg ambient.hwg ambient.hcube ambient.hdegree ambient.hrowsD ambient.htail
    (fun j i => ambient.hblocks ⟨j, Sum.inr i⟩) ambient.hRv ambient.hRiGrid ambient.hδw ambient.hcoeff
    ambient.haxesGrid ambient.hfullAxes ambient.hfullOutputs ambient.hambientCount ambient.hprofileBudget
    ambient.hBanalytic ambient.hDanalytic ambient.hcutoffAnalytic ambient.hcoordAnalytic ambient.hgridAnalytic
    hMaster ambient.hI ambient.hn ambient.hcoeffEarly ambient.hRiEarly ambient.hVEarly

end Erdos3.VectorPolynomial

end

end OAI

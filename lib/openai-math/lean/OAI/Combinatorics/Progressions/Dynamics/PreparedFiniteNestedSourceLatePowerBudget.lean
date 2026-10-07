import OAI.Combinatorics.Progressions.Estimates.EmptyLayerPrescribedScale
import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleWitnessScalarPower
import OAI.Combinatorics.Progressions.Polynomial.PreparedFiniteNestedForwardAllDegreePaddedSource

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

theorem probabilityProfileLipschitz_eight_le_exp :
    8 * (probabilityProfileLipschitz : ℝ) ≤
      Real.exp ((probabilityProfileLipschitz : ℝ) + 8) := by
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hprofile : (probabilityProfileLipschitz : ℝ) ≤
      Real.exp (probabilityProfileLipschitz : ℝ) := by
    linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
  calc
    _ ≤ Real.exp 8 * Real.exp (probabilityProfileLipschitz : ℝ) :=
      mul_le_mul h8 hprofile (NNReal.coe_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, add_comm]

noncomputable def emptyLayerTailFixedLog (m d : ℕ) : ℝ :=
  (probabilityProfileLipschitz : ℝ) + 8 +
    (allocatedComparisonDimension m (d : ℝ) + 4)

theorem emptyLayerTailFixedLog_nonneg (m d : ℕ) :
    0 ≤ emptyLayerTailFixedLog m d := by
  have hD := (allocatedComparisonDimension_bounds m (Nat.cast_nonneg d)).1
  unfold emptyLayerTailFixedLog
  positivity

variable {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, IsEmpty (I j)]
    {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem emptyLayerTailScaleFloor_le_exp
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {pRadius Pscale : ℝ}
    (hradius : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (htolerance : ∀ j, (σ j)⁻¹ ≤ Real.exp Pscale) :
    ∀ j, layerSamplerTailScaleFloor (G := G) B R σ j ≤
      Real.exp ((probabilityProfileLipschitz : ℝ) + 8 +
        (allocatedComparisonDimension m (Fintype.card G : ℝ) + 4) + pRadius + Pscale) :=
  layerSamplerTailScaleFloor_le_exp B hR hσ
    probabilityProfileLipschitz_eight_le_exp (emptyLayerCoefficientCount_le_exp B)
    hradius htolerance

theorem exists_emptyLayerTailFixedLog_power_budget (m d inputPower : ℕ) :
    ∃ outputPower : ℕ, 2 ≤ outputPower ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ pRadius Pscale : ℝ,
        pRadius ≤ (p + 2) ^ inputPower →
        Pscale ≤ (p + 2) ^ inputPower →
        emptyLayerTailFixedLog m d + pRadius + Pscale ≤ (p + 2) ^ outputPower := by
  let bound : Polynomial ℕ := Polynomial.C ⌈emptyLayerTailFixedLog m d⌉₊ +
    2 * (Polynomial.X + 2) ^ inputPower
  obtain ⟨outputPower, houtputPower, hbound⟩ := exists_natPolynomial_fixed_power_budget bound
  refine ⟨outputPower, houtputPower, ?_⟩
  intro p hp pRadius Pscale hRadius hScale
  have hmajor : (⌈emptyLayerTailFixedLog m d⌉₊ : ℝ) +
      2 * (p + 2) ^ inputPower ≤ (p + 2) ^ outputPower := by
    simpa [bound, Polynomial.eval₂_pow] using hbound p hp
  have hfixed := Nat.le_ceil (emptyLayerTailFixedLog m d)
  linarith

theorem exists_emptyLayerTailScaleFloor_power_budget (inputPower : ℕ) :
    ∃ outputPower : ℕ, 2 ≤ outputPower ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ (R σ : Fin m → ℝ), (∀ j, 0 < R j) → (∀ j, 0 < σ j) →
      ∀ pRadius Pscale : ℝ,
        pRadius ≤ (p + 2) ^ inputPower →
        Pscale ≤ (p + 2) ^ inputPower →
        (∀ j, (R j)⁻¹ ≤ Real.exp pRadius) →
        (∀ j, (σ j)⁻¹ ≤ Real.exp Pscale) →
        ∀ j, layerSamplerTailScaleFloor (G := G) B R σ j ≤
          Real.exp ((p + 2) ^ outputPower) := by
  obtain ⟨outputPower, houtputPower, hbound⟩ :=
    exists_emptyLayerTailFixedLog_power_budget m (Fintype.card G) inputPower
  refine ⟨outputPower, houtputPower, ?_⟩
  intro p hp R σ hR hσ pRadius Pscale hRadius hScale hradius htolerance j
  apply (emptyLayerTailScaleFloor_le_exp B hR hσ hradius htolerance j).trans
  exact Real.exp_le_exp.mpr (hbound hp pRadius Pscale hRadius hScale)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem PreparedModularCanonicalDetectorResources.Bounds.mono
    {r : PreparedModularCanonicalDetectorResources ℝ} {B C : ℝ}
    (h : r.Bounds B) (hBC : B ≤ C) : r.Bounds C := by
  have lift {a : ℝ} (ha : a ∈ Set.Icc 0 B) : a ∈ Set.Icc 0 C :=
    ⟨ha.1, ha.2.trans hBC⟩
  cases h
  constructor <;> apply lift <;> assumption

theorem exists_preparedModularGeneral_cutoff_resource_budget (m cutoff : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P L : ℝ}, 0 ≤ P → P ≤ L → ∀ degree : ℕ,
      degree ≤ cutoff →
      let r := preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants m degree) (degree + 1) P L
      r.Bounds ((P + L + C) ^ C) := by
  let K (degree : Fin (cutoff + 1)) := preparedModularGeneralDetectorConstants m degree.val
  let A (degree : Fin (cutoff + 1)) := Classical.choose
    (exists_preparedModularGeneralDetector_resource_budget (K degree) (degree.val + 1))
  let poly : Polynomial ℕ := ∑ degree : Fin (cutoff + 1),
    (Polynomial.X + Polynomial.C (A degree)) ^ A degree
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro P L hP hPL degree hdegree r
  let i : Fin (cutoff + 1) := ⟨degree, Nat.lt_succ_of_le hdegree⟩
  have hsum : (P + L + A i) ^ A i ≤
      ∑ j : Fin (cutoff + 1), (P + L + A j) ^ A j :=
    Finset.single_le_sum
      (f := fun j : Fin (cutoff + 1) => (P + L + (A j : ℝ)) ^ A j)
      (fun j _ => by have hL := hP.trans hPL; positivity) (Finset.mem_univ i)
  have hbound : (P + L + A i) ^ A i ≤ (P + L + C) ^ C := by
    apply hsum.trans
    simpa [poly, Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow] using
      hpoly (P + L) (add_nonneg hP (hP.trans hPL))
  have hstage := ((Classical.choose_spec
    (exists_preparedModularGeneralDetector_resource_budget (K i) (i.val + 1))).2 hP hPL).1
  exact hstage.mono hbound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

def PreparedEmptyLayerLocalScheduleBudget
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ requestedCoarse extraLate : ℝ)
    (u model : K → ℝ) (cap : ℝ) : Prop :=
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (u k) (model k)
  let aDetect := fun k => 2 * u k + 4 * model k + 7
  let gain := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (gain k + pDetect k + 4)
  let physical := fun k => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => gain k + 40 + coefficientErrorSpatialLog (physical k)
  let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let rho := fun k => 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
  let tail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
  let scale := preparedUniformDegreeScaleLog (D + pRadius) tail Qσ
  let tmod := fun k => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
  let lengths := fun k => allocatedAffineLengthLog m D scale (rho k) (Pk k)
    (target k) (pDetect k + 2) (tmod k)
  let master := fun k => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
    (physical k) (u k) (model k) (rho k) (target k) (gain k)
  let coarse := preparedFiniteScheduleDirectCoarse gain requestedCoarse
  let late := ∑ k, preparedUniformDegreeDirectLate (master k) scale (physical k) coarse extraLate
  pRadius ∈ Set.Icc 0 cap ∧ D ∈ Set.Icc 0 cap ∧ scale ∈ Set.Icc 0 cap ∧
    coarse ∈ Set.Icc 0 cap ∧ late ∈ Set.Icc 0 cap ∧
    ∀ k, gain k ∈ Set.Icc 0 cap ∧ Pk k ∈ Set.Icc 0 cap ∧
      physical k ∈ Set.Icc 0 cap ∧ target k ∈ Set.Icc 0 cap ∧
      rho k ∈ Set.Icc 0 cap ∧ tail k ∈ Set.Icc 0 cap ∧
      lengths k ∈ Set.Icc 0 cap ∧ master k ∈ Set.Icc 0 cap ∧
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (master k) late).Bounds cap

theorem PreparedEmptyLayerLocalScheduleBudget.mono
    {m : ℕ} {K G : Type} [Fintype K] [Fintype G]
    {degree Cdetect : K → ℕ} {nX count : ℕ}
    {Bstruct pnum Qstride Qσ requestedCoarse extraLate : ℝ}
    {u model : K → ℝ} {cap cap' : ℝ}
    (h : PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ requestedCoarse extraLate u model cap) (hcap : cap ≤ cap') :
    PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ requestedCoarse extraLate u model cap' := by
  unfold PreparedEmptyLayerLocalScheduleBudget at h ⊢
  dsimp only at h ⊢
  have lift {x : ℝ} (hx : x ∈ Set.Icc 0 cap) : x ∈ Set.Icc 0 cap' := ⟨hx.1, hx.2.trans hcap⟩
  refine ⟨lift h.1, lift h.2.1, lift h.2.2.1, lift h.2.2.2.1, lift h.2.2.2.2.1, ?_⟩
  intro k
  obtain ⟨hg, hk, hp, ht, hr, htail, hl, hm, hres⟩ := h.2.2.2.2.2 k
  exact ⟨lift hg, lift hk, lift hp, lift ht, lift hr, lift htail, lift hl, lift hm,
    hres.mono hcap⟩

theorem exists_preparedEmptyLayerLocalSchedule_budget (m nStages Cmax : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {K G : Type} [Fintype K] [Fintype G]
      (degree Cdetect : K → ℕ) {nX count : ℕ}
      {P Bstruct pnum Qstride Qσ requestedCoarse extraLate : ℝ}
      (u model : K → ℝ),
      Fintype.card K ≤ nStages → (∀ k, degree k ≤ m) → (∀ k, Cdetect k ≤ Cmax) →
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P → Qσ ∈ Set.Icc 0 P →
      requestedCoarse ∈ Set.Icc 0 P → extraLate ∈ Set.Icc 0 P →
      (∀ k, u k ∈ Set.Icc 0 P) → (∀ k, model k ∈ Set.Icc 0 P) →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
        Bstruct pnum Qstride Qσ requestedCoarse extraLate u model ((P + 2) ^ C) := by
  obtain ⟨A, _, hEarly⟩ := exists_preparedFiniteScheduleEarlyBudget m nStages Cmax
  obtain ⟨B, _, hGeom⟩ := exists_preparedFiniteScheduleGeometryBudget m nStages Cmax
  obtain ⟨R, _, hResources⟩ := exists_preparedModularGeneral_cutoff_resource_budget m m
  let X : Polynomial ℕ := Polynomial.X
  let rawPoly := 7 * X + 12
  let earlyPoly := (rawPoly + Polynomial.C A) ^ A
  let physicalPoly := Polynomial.C (m + 2) + 3 * X + earlyPoly
  let precisionPoly := rawPoly + earlyPoly + physicalPoly + 40 + coefficientErrorSpatialLog physicalPoly
  let geomPoly := (precisionPoly + Polynomial.C B) ^ B
  let masterPoly := 11 * geomPoly + 32
  let coarsePoly := Polynomial.C nStages * (geomPoly + 32) + X
  let spatialPoly := spatialPrimitiveEnvelope geomPoly coarsePoly 0
  let latePoly := masterPoly + geomPoly + coarsePoly +
    (2 * (spatialPoly + spatialTupleToleranceLog spatialPoly) + 4) + X
  let sumLatePoly := Polynomial.C nStages * latePoly
  let resourcesPoly := (masterPoly + sumLatePoly + Polynomial.C R) ^ R
  obtain ⟨C, hC, hPoly⟩ := exists_natPolynomial_fixed_power_budget
    (geomPoly + masterPoly + coarsePoly + sumLatePoly + resourcesPoly)
  refine ⟨C, hC, ?_⟩
  intro K G _ _ degree Cdetect nX count P Bstruct pnum Qstride Qσ requestedCoarse extraLate
    u model hCard hdegree hCdetect hP hB hnum hQ hQσ hCoarse hExtra hu hmodel hcount hnX hG
  unfold PreparedEmptyLayerLocalScheduleBudget
  intro pRadius D pDetect aDetect gain Pk physical target E rho tail scale tmod lengths master coarse late
  let raw : ℝ := 7 * P + 12
  let early : ℝ := (raw + A) ^ A
  let physicalBound : ℝ := ((m + 2 : ℕ) : ℝ) + 3 * P + early
  let precision : ℝ := raw + early + physicalBound + 40 + coefficientErrorSpatialLog physicalBound
  let geom : ℝ := (precision + B) ^ B
  let masterBound : ℝ := 11 * geom + 32
  let coarseBound : ℝ := (nStages : ℝ) * (geom + 32) + P
  let spatial : ℝ := spatialPrimitiveEnvelope geom coarseBound 0
  let lateBound : ℝ := masterBound + geom + coarseBound +
    (2 * (spatial + spatialTupleToleranceLog spatial) + 4) + P
  let sumLateBound : ℝ := (nStages : ℝ) * lateBound
  let resourceBound : ℝ := (masterBound + sumLateBound + R) ^ R
  have hraw0 : 0 ≤ raw := by dsimp [raw]; positivity
  have hPraw : P ≤ raw := by dsimp [raw]; linarith
  have liftRaw {x : ℝ} (hx : x ∈ Set.Icc 0 P) : x ∈ Set.Icc 0 raw :=
    ⟨hx.1, hx.2.trans hPraw⟩
  have hp (k) : pDetect k ∈ Set.Icc 0 raw := by
    dsimp only [pDetect, allocatedModelTestLog, raw]
    constructor <;> linarith only [(hu k).1, (hu k).2, (hmodel k).1, (hmodel k).2]
  have ha (k) : aDetect k ∈ Set.Icc 0 raw := by
    dsimp only [aDetect, raw]
    constructor <;> linarith only [(hu k).1, (hu k).2, (hmodel k).1, (hmodel k).2, hP]
  obtain ⟨hrawEarly, _, _, hStageEarly⟩ :=
    hEarly degree Cdetect (G := G) pDetect aDetect (fun _ => 0)
      hCard hdegree hCdetect hraw0 (liftRaw hB) (liftRaw hnum) hp ha (liftRaw hQ)
      (fun _ => ⟨le_rfl, hraw0⟩) (hcount.trans hPraw) (hnX.trans hPraw) (hG.trans hPraw)
  have hgain (k) : gain k ∈ Set.Icc 0 early := (hStageEarly k).1
  have hkernel (k) : Pk k ∈ Set.Icc 0 early := (hStageEarly k).2.1
  have hearly0 : 0 ≤ early := hraw0.trans hrawEarly
  have hphysicalBound0 : 0 ≤ physicalBound := by dsimp [physicalBound]; positivity
  have hphysical (k) : physical k ∈ Set.Icc 0 physicalBound := by
    dsimp only [physical, preparedFiniteScheduleLocalPhysical, physicalBound]
    constructor
    · have := hQ.1; have := (hkernel k).1; positivity
    · linarith only [hnX, hcount, hQ.2, (hkernel k).2]
  have hprecision0 : 0 ≤ precision := by
    have := coefficientErrorSpatialLog_nonneg hphysicalBound0
    dsimp only [precision]; positivity
  have hrawPrecision : raw ≤ precision := by
    have := coefficientErrorSpatialLog_nonneg hphysicalBound0
    dsimp only [precision]; linarith
  have hearlyPrecision : early ≤ precision := by
    have := coefficientErrorSpatialLog_nonneg hphysicalBound0
    dsimp only [precision]; linarith
  have htarget (k) : target k ∈ Set.Icc 0 precision := by
    have hsp : coefficientErrorSpatialLog (physical k) ≤ coefficientErrorSpatialLog physicalBound := by
      have := (hphysical k).1
      unfold coefficientErrorSpatialLog coefficientErrorVolumeLog anisotropicSpatialCapLog
      gcongr <;> exact (hphysical k).2
    constructor
    · have := (hgain k).1
      have := coefficientErrorSpatialLog_nonneg (hphysical k).1
      dsimp only [target]; positivity
    · dsimp only [target, precision]
      linarith only [(hgain k).2, hsp, hraw0, hphysicalBound0]
  have hPprecision : P ≤ precision := hPraw.trans hrawPrecision
  have liftPrecision {x : ℝ} (hx : x ∈ Set.Icc 0 P) : x ∈ Set.Icc 0 precision :=
    ⟨hx.1, hx.2.trans hPprecision⟩
  obtain ⟨hprecisionGeom, hradius, hD, hStage, hscale, hlengthSum, _, _⟩ :=
    hGeom degree Cdetect (G := G) pDetect aDetect target
      hCard hdegree hCdetect hprecision0 (liftPrecision hB) (liftPrecision hnum)
      (fun k => ⟨(hp k).1, (hp k).2.trans hrawPrecision⟩)
      (fun k => ⟨(ha k).1, (ha k).2.trans hrawPrecision⟩)
      (liftPrecision hQ) htarget (hcount.trans hPprecision) (hnX.trans hPprecision)
      (hG.trans hPprecision) (liftPrecision hQσ) ⟨le_rfl, hprecision0⟩ ⟨le_rfl, hprecision0⟩
  change precision ≤ geom at hprecisionGeom
  change pRadius ∈ Set.Icc 0 geom at hradius
  change D ∈ Set.Icc 0 geom at hD
  change (∀ k, gain k ∈ Set.Icc 0 geom ∧ Pk k ∈ Set.Icc 0 geom ∧
    rho k ∈ Set.Icc 0 geom ∧ tail k ∈ Set.Icc 0 geom ∧ tmod k ∈ Set.Icc 0 geom) at hStage
  change scale ∈ Set.Icc 0 geom at hscale
  change (∑ k, lengths k) ∈ Set.Icc 0 geom at hlengthSum
  have hgeom0 : 0 ≤ geom := hprecision0.trans hprecisionGeom
  have hPgeom : P ≤ geom := hPprecision.trans hprecisionGeom
  have hpGeom (k) : pDetect k ∈ Set.Icc 0 geom :=
    ⟨(hp k).1, (hp k).2.trans (hrawPrecision.trans hprecisionGeom)⟩
  have hphysicalGeom (k) : physical k ∈ Set.Icc 0 geom := by
    refine ⟨(hphysical k).1, ?_⟩
    have hbase : physicalBound ≤ precision := by
      have hspatial := coefficientErrorSpatialLog_nonneg hphysicalBound0
      dsimp only [precision]
      linarith only [hspatial, hraw0, hearly0]
    exact (hphysical k).2.trans (hbase.trans hprecisionGeom)
  have htargetGeom (k) : target k ∈ Set.Icc 0 geom :=
    ⟨(htarget k).1, (htarget k).2.trans hprecisionGeom⟩
  have hlength (k) : lengths k ∈ Set.Icc 0 geom := by
    have hnonneg (j) : 0 ≤ lengths j :=
      (allocatedAffineLengthLog_bounds m hD.1 hscale.1 (hStage j).2.2.1.1
        (hStage j).2.1.1 (htarget j).1 (by linarith only [(hp j).1])
        (hStage j).2.2.2.2.1).2.2.1
    exact ⟨hnonneg k, (Finset.single_le_sum (fun j _ => hnonneg j)
      (Finset.mem_univ k)).trans hlengthSum.2⟩
  have hmaster (k) : master k ∈ Set.Icc 0 masterBound := by
    change 0 ≤ Bstruct + D + pRadius + Qstride + physical k +
      (u k + model k + pDetect k + rho k + target k + gain k + 32) ∧ _
    constructor
    · have := hB.1; have := hD.1; have := hradius.1; have := hQ.1
      have := (hphysical k).1; have := (hu k).1; have := (hmodel k).1
      have := (hp k).1; have := (hStage k).2.2.1.1; have := (htarget k).1
      have := (hgain k).1; positivity
    · change Bstruct + D + pRadius + Qstride + physical k +
        (u k + model k + pDetect k + rho k + target k + gain k + 32) ≤ 11 * geom + 32
      linarith only [hB.2.trans hPgeom, hD.2, hradius.2, hQ.2.trans hPgeom,
        (hphysicalGeom k).2, (hu k).2.trans hPgeom, (hmodel k).2.trans hPgeom,
        (hpGeom k).2, (hStage k).2.2.1.2, (htargetGeom k).2, (hStage k).1.2]
  have hmasterBound0 : 0 ≤ masterBound := by dsimp [masterBound]; positivity
  have hcoarseBound0 : 0 ≤ coarseBound := by dsimp [coarseBound]; positivity
  have hcoarse : coarse ∈ Set.Icc 0 coarseBound := by
    have hsum : (∑ k, (gain k + 32)) ≤ (nStages : ℝ) * (geom + 32) := by
      calc
        _ ≤ ∑ _k : K, (geom + 32) := Finset.sum_le_sum (fun k _ => by linarith [(hStage k).1.2])
        _ = (Fintype.card K : ℝ) * (geom + 32) := by simp [mul_add]
        _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hCard) (by positivity)
    exact ⟨hCoarse.1.trans (le_max_right _ _), max_le
      (hsum.trans (le_add_of_nonneg_right hP))
      (hCoarse.2.trans (le_add_of_nonneg_left (by positivity)))⟩
  have hspatial0 : 0 ≤ spatial := (spatialPrimitiveEnvelope_bounds hgeom0 hcoarseBound0 (le_refl 0)).1
  have hlateBound0 : 0 ≤ lateBound := by
    have ht : 0 ≤ spatialTupleToleranceLog spatial := by unfold spatialTupleToleranceLog; positivity
    dsimp only [lateBound]; positivity
  have hsumLateBound0 : 0 ≤ sumLateBound := mul_nonneg (Nat.cast_nonneg _) hlateBound0
  have hlocalLate (k) : preparedUniformDegreeDirectLate (master k) scale (physical k) coarse extraLate
      ∈ Set.Icc 0 lateBound := by
    have hsp : spatialPrimitiveEnvelope (physical k) coarse 0 ≤ spatial :=
      spatialPrimitiveEnvelope_mono (hphysicalGeom k).1 hcoarse.1 (le_refl 0)
        (hphysicalGeom k).2 hcoarse.2 (le_refl 0)
    have hsp0 := (spatialPrimitiveEnvelope_bounds (hphysical k).1 hcoarse.1 (le_refl 0)).1
    have ht : spatialTupleToleranceLog (spatialPrimitiveEnvelope (physical k) coarse 0) ≤
        spatialTupleToleranceLog spatial := by unfold spatialTupleToleranceLog; gcongr
    have hxi : 2 * (spatialPrimitiveEnvelope (physical k) coarse 0 +
        spatialTupleToleranceLog (spatialPrimitiveEnvelope (physical k) coarse 0)) + 4 ≤
        2 * (spatial + spatialTupleToleranceLog spatial) + 4 := by linarith
    have hxi0 : 0 ≤ 2 * (spatial + spatialTupleToleranceLog spatial) + 4 := by
      unfold spatialTupleToleranceLog; positivity
    refine ⟨(hmaster k).1.trans (le_max_left _ _), ?_⟩
    unfold preparedUniformDegreeDirectLate
    apply max_le _ (max_le _ (max_le _ (max_le _ _))) <;>
      dsimp only [lateBound] <;>
      linarith only [(hmaster k).2, hscale.2, hcoarse.2, hxi, hExtra.2,
        hmasterBound0, hgeom0, hcoarseBound0, hxi0, hP]
  have hlate : late ∈ Set.Icc 0 sumLateBound := by
    refine ⟨Finset.sum_nonneg (fun k _ => (hlocalLate k).1), ?_⟩
    calc
      _ ≤ ∑ _k : K, lateBound := Finset.sum_le_sum (fun k _ => (hlocalLate k).2)
      _ = (Fintype.card K : ℝ) * lateBound := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hCard) hlateBound0
  have hmasterLate (k) : master k ≤ late :=
    (le_max_left _ _).trans (Finset.single_le_sum (fun j _ => (hlocalLate j).1) (Finset.mem_univ k))
  have hresourceBound0 : 0 ≤ resourceBound := by dsimp [resourceBound]; positivity
  let ev : Polynomial ℕ →+* ℝ := Polynomial.eval₂RingHom (Nat.castRingHom ℝ) P
  have heX : ev X = P := by simp [ev, X]
  have heC (n : ℕ) : ev (Polynomial.C n) = (n : ℝ) := by simp [ev]
  have heRaw : ev rawPoly = raw := by
    simp only [rawPoly, map_add, map_mul, map_ofNat, heX, raw]
  have heEarly : ev earlyPoly = early := by
    simp only [earlyPoly, map_pow, map_add, heRaw, heC, early]
  have hePhysical : ev physicalPoly = physicalBound := by
    simp only [physicalPoly, map_add, map_mul, heC, map_ofNat, heX, heEarly, physicalBound, Nat.cast_add, Nat.cast_ofNat]
  have hePrecision : ev precisionPoly = precision := by
    simp only [precisionPoly, map_add, map_ofNat, heRaw, heEarly, hePhysical,
      map_coefficientErrorSpatialLog, precision]
  have heGeom : ev geomPoly = geom := by
    simp only [geomPoly, map_pow, map_add, hePrecision, heC, geom]
  have heMaster : ev masterPoly = masterBound := by
    simp only [masterPoly, map_add, map_mul, map_ofNat, heGeom, masterBound]
  have heCoarse : ev coarsePoly = coarseBound := by
    simp only [coarsePoly, map_add, map_mul, map_ofNat, heGeom, heC, heX, coarseBound]
  have heSpatial : ev spatialPoly = spatial := by
    simp only [spatialPoly, map_spatialPrimitiveEnvelope, heGeom, heCoarse, map_zero, spatial]
  have heLate : ev latePoly = lateBound := by
    simp only [latePoly, map_add, map_mul, map_ofNat, heMaster, heGeom, heCoarse,
      heSpatial, map_spatialTupleToleranceLog, heX, lateBound]
  have heSumLate : ev sumLatePoly = sumLateBound := by
    simp only [sumLatePoly, map_mul, heC, heLate, sumLateBound]
  have heResource : ev resourcesPoly = resourceBound := by
    simp only [resourcesPoly, map_pow, map_add, heMaster, heSumLate, heC, resourceBound]
  have htotal := hPoly P hP
  change ev (geomPoly + masterPoly + coarsePoly + sumLatePoly + resourcesPoly) ≤ (P + 2) ^ C at htotal
  simp only [map_add, heGeom, heMaster, heCoarse, heSumLate, heResource] at htotal
  have hgeomCap : geom ≤ (P + 2) ^ C := by linarith only [htotal, hmasterBound0, hcoarseBound0, hsumLateBound0, hresourceBound0]
  have hmasterCap : masterBound ≤ (P + 2) ^ C := by linarith only [htotal, hgeom0, hcoarseBound0, hsumLateBound0, hresourceBound0]
  have hcoarseCap : coarseBound ≤ (P + 2) ^ C := by linarith only [htotal, hgeom0, hmasterBound0, hsumLateBound0, hresourceBound0]
  have hlateCap : sumLateBound ≤ (P + 2) ^ C := by linarith only [htotal, hgeom0, hmasterBound0, hcoarseBound0, hresourceBound0]
  have hresourceCap : resourceBound ≤ (P + 2) ^ C := by linarith only [htotal, hgeom0, hmasterBound0, hcoarseBound0, hsumLateBound0]
  have lift {x : ℝ} (hx : x ∈ Set.Icc 0 geom) : x ∈ Set.Icc 0 ((P + 2) ^ C) := ⟨hx.1, hx.2.trans hgeomCap⟩
  refine ⟨lift hradius, lift hD, lift hscale, ⟨hcoarse.1, hcoarse.2.trans hcoarseCap⟩,
    ⟨hlate.1, hlate.2.trans hlateCap⟩, ?_⟩
  intro k
  have hres := hResources (hmaster k).1 (hmasterLate k) (degree k) (hdegree k)
  have hresCap : (master k + late + R) ^ R ≤ (P + 2) ^ C := by
    apply le_trans _ hresourceCap
    apply pow_le_pow_left₀ (by have := (hmaster k).1; have := hlate.1; positivity)
    linarith only [(hmaster k).2, hlate.2]
  exact ⟨lift (hStage k).1, lift (hStage k).2.1, lift (hphysicalGeom k),
    lift (htargetGeom k), lift (hStage k).2.2.1, lift (hStage k).2.2.2.1,
    lift (hlength k), ⟨(hmaster k).1, (hmaster k).2.trans hmasterCap⟩, hres.mono hresCap⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators NNReal

noncomputable def preparedEmptyLayerLocalTailWidthLog
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ : ℝ) (u model : K → ℝ) : ℝ :=
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (u k) (model k)
  let aDetect := fun k => 2 * u k + 4 * model k + 7
  let gain := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (gain k + pDetect k + 4)
  let physical := fun k => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => gain k + 40 + coefficientErrorSpatialLog (physical k)
  let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let tail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
  let scale := preparedUniformDegreeScaleLog (D + pRadius) tail Qσ
  (probabilityProfileLipschitz : ℝ) + 8 + (D + 4) + pRadius + scale

theorem PreparedEmptyLayerLocalScheduleBudget.tailWidthLog_le
    {m : ℕ} {K G : Type} [Fintype K] [Fintype G]
    {degree Cdetect : K → ℕ} {nX count : ℕ}
    {Bstruct pnum Qstride Qσ requestedCoarse extraLate : ℝ}
    {u model : K → ℝ} {cap : ℝ}
    (h : PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ requestedCoarse extraLate u model cap) :
    preparedEmptyLayerLocalTailWidthLog (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ u model ≤
        (probabilityProfileLipschitz : ℝ) + 12 + 3 * cap := by
  unfold PreparedEmptyLayerLocalScheduleBudget at h
  dsimp only at h
  unfold preparedEmptyLayerLocalTailWidthLog
  dsimp only
  linarith only [h.1.2, h.2.1.2, h.2.2.1.2]

theorem PreparedEmptyLayerLocalScheduleBudget.tailWidthLog_nonneg
    {m : ℕ} {K G : Type} [Fintype K] [Fintype G]
    {degree Cdetect : K → ℕ} {nX count : ℕ}
    {Bstruct pnum Qstride Qσ requestedCoarse extraLate : ℝ}
    {u model : K → ℝ} {cap : ℝ}
    (h : PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ requestedCoarse extraLate u model cap) :
    0 ≤ preparedEmptyLayerLocalTailWidthLog (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ u model := by
  unfold PreparedEmptyLayerLocalScheduleBudget at h
  dsimp only at h
  unfold preparedEmptyLayerLocalTailWidthLog
  dsimp only
  linarith only [h.1.1, h.2.1.1, h.2.2.1.1, NNReal.coe_nonneg probabilityProfileLipschitz]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedFiniteScheduleWitnessSeed
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ Pmin : ℝ) (u model : K → ℝ) : ℝ :=
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (u k) (model k)
  let aDetect := fun k => 2 * u k + 4 * model k + 7
  let gain := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (gain k + pDetect k + 4)
  let physical := fun k => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => gain k + 40 + coefficientErrorSpatialLog (physical k)
  let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let rho := fun k => 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
  let tail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
  let scale := preparedUniformDegreeScaleLog (D + pRadius) tail Qσ
  let tmod := fun k => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
  let lengths := fun k => allocatedAffineLengthLog m D scale (rho k) (Pk k)
    (target k) (pDetect k + 2) (tmod k)
  allocatedScaleLog (scale + ∑ k, lengths k + Pmin + 1)

def PreparedFiniteScheduleWitnessBudget
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ Pmin Qw requestedCoarse : ℝ)
    (u model : K → ℝ) (cap : ℝ) : Prop :=
  let seed := preparedFiniteScheduleWitnessSeed (G := G) m degree Cdetect nX count
    Bstruct pnum Qstride Qσ Pmin u model
  seed ∈ Set.Icc 0 cap ∧ allocatedWitnessScaleLog seed Qw ∈ Set.Icc 0 cap ∧
    PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ requestedCoarse (allocatedWitnessScaleLog seed Qw) u model cap

theorem exists_preparedFiniteScheduleWitnessLate_power_budget
    (m nStages Cmax inputPower : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {K G : Type} [Fintype K] [Fintype G]
        (degree Cdetect : K → ℕ) {nX count : ℕ}
        {B Bstruct pnum Qstride Qσ Pmin Qw requestedCoarse : ℝ}
        (u model : K → ℝ),
        Fintype.card K ≤ nStages → (∀ k, degree k ≤ m) → (∀ k, Cdetect k ≤ Cmax) →
        0 ≤ B → Bstruct ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        pnum ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        Qstride ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        Qσ ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        Pmin ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        Qw ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        requestedCoarse ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        (∀ k, u k ∈ Set.Icc 0 ((B + 2) ^ inputPower)) →
        (∀ k, model k ∈ Set.Icc 0 ((B + 2) ^ inputPower)) →
        (count : ℝ) ≤ (B + 2) ^ inputPower →
        (nX : ℝ) ≤ (B + 2) ^ inputPower →
        (Fintype.card G : ℝ) ≤ (B + 2) ^ inputPower →
        PreparedFiniteScheduleWitnessBudget (G := G) m degree Cdetect nX count
          Bstruct pnum Qstride Qσ Pmin Qw requestedCoarse u model ((B + 2) ^ C) := by
  obtain ⟨D0, _, hlocal⟩ := exists_preparedEmptyLayerLocalSchedule_budget m nStages Cmax
  let T : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower
  obtain ⟨A, _, hfirstBound⟩ := exists_natPolynomial_fixed_power_budget
    (T + (T + 2) ^ D0)
  obtain ⟨W, _, hwitness⟩ := exists_preparedFiniteScheduleWitnessScalar_power_budget nStages A
  let nextPower := A + W
  let Final : Polynomial ℕ :=
    (Polynomial.X + 2) ^ W + ((Polynomial.X + 2) ^ nextPower + 2) ^ D0
  obtain ⟨C, hC, hfinalBound⟩ := exists_natPolynomial_fixed_power_budget Final
  refine ⟨C, hC, ?_⟩
  intro K G _ _ degree Cdetect nX count B Bstruct pnum Qstride Qσ Pmin Qw requestedCoarse
    u model hcard hdegree hdetect hB hstruct hnum hstride hσ hmin hQw hrequested
    hu hmodel hcount hnX hG
  let t : ℝ := (B + 2) ^ inputPower
  let first : ℝ := (t + 2) ^ D0
  let early : ℝ := (B + 2) ^ A
  let witnessCap : ℝ := (B + 2) ^ W
  let next : ℝ := (B + 2) ^ nextPower
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hfirst0 : 0 ≤ first := by dsimp only [first]; positivity
  have hearly0 : 0 ≤ early := by dsimp only [early]; positivity
  have hwitness0 : 0 ≤ witnessCap := by dsimp only [witnessCap]; positivity
  have hnext0 : 0 ≤ next := by dsimp only [next]; positivity
  have hfirstSum : t + first ≤ early := by
    simpa [T, t, first, early, Polynomial.eval₂_pow] using hfirstBound B hB
  have htEarly : t ≤ early := by linarith only [hfirstSum, hfirst0]
  have hfirstEarly : first ≤ early := by linarith only [hfirstSum, ht]
  have liftEarly {x : ℝ} (hx : x ∈ Set.Icc 0 t) : x ∈ Set.Icc 0 early :=
    ⟨hx.1, hx.2.trans htEarly⟩
  have hinitial := hlocal (G := G) degree Cdetect u model hcard hdegree hdetect ht
    hstruct hnum hstride hσ hrequested (show (0 : ℝ) ∈ Set.Icc 0 t from ⟨le_rfl, ht⟩)
    hu hmodel hcount hnX hG
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (u k) (model k)
  let aDetect := fun k => 2 * u k + 4 * model k + 7
  let gain := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (gain k + pDetect k + 4)
  let physical := fun k => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => gain k + 40 + coefficientErrorSpatialLog (physical k)
  let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let rho := fun k => 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
  let tail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
  let scale := preparedUniformDegreeScaleLog (D + pRadius) tail Qσ
  let tmod := fun k => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
  let lengths := fun k => allocatedAffineLengthLog m D scale (rho k) (Pk k)
    (target k) (pDetect k + 2) (tmod k)
  let seed := allocatedScaleLog (scale + ∑ k, lengths k + Pmin + 1)
  have hscale : scale ∈ Set.Icc 0 first := hinitial.2.2.1
  have hlength (k : K) : lengths k ∈ Set.Icc 0 first := by
    obtain ⟨_, _, _, _, _, _, hl, _, _⟩ := hinitial.2.2.2.2.2 k
    exact hl
  have hseedWitness := hwitness (Pscale := scale) lengths hcard hB
    ⟨hscale.1, hscale.2.trans hfirstEarly⟩ (liftEarly hmin) (liftEarly hQw)
    (fun k => ⟨(hlength k).1, (hlength k).2.trans hfirstEarly⟩)
  change seed ∈ Set.Icc 0 witnessCap ∧
    allocatedWitnessScaleLog seed Qw ∈ Set.Icc 0 witnessCap at hseedWitness
  have hearlyNext : early ≤ next :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ B + 2) (Nat.le_add_right A W)
  have hwitnessNext : witnessCap ≤ next :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ B + 2) (Nat.le_add_left W A)
  have htNext : t ≤ next := htEarly.trans hearlyNext
  have liftNext {x : ℝ} (hx : x ∈ Set.Icc 0 t) : x ∈ Set.Icc 0 next :=
    ⟨hx.1, hx.2.trans htNext⟩
  have hactual := hlocal (G := G) degree Cdetect u model hcard hdegree hdetect hnext0
    (liftNext hstruct) (liftNext hnum) (liftNext hstride) (liftNext hσ)
    (liftNext hrequested) ⟨hseedWitness.2.1, hseedWitness.2.2.trans hwitnessNext⟩
    (fun k => liftNext (hu k)) (fun k => liftNext (hmodel k))
    (hcount.trans htNext) (hnX.trans htNext) (hG.trans htNext)
  have hfinalSum : witnessCap + (next + 2) ^ D0 ≤ (B + 2) ^ C := by
    simpa [Final, witnessCap, next, Polynomial.eval₂_pow] using hfinalBound B hB
  have hnextPower0 : 0 ≤ (next + 2) ^ D0 := by positivity
  have hwitnessFinal : witnessCap ≤ (B + 2) ^ C := by
    linarith only [hfinalSum, hnextPower0]
  have hactualFinal : (next + 2) ^ D0 ≤ (B + 2) ^ C := by
    linarith only [hfinalSum, hwitness0]
  change seed ∈ Set.Icc 0 ((B + 2) ^ C) ∧
    allocatedWitnessScaleLog seed Qw ∈ Set.Icc 0 ((B + 2) ^ C) ∧ _
  exact ⟨⟨hseedWitness.1.1, hseedWitness.1.2.trans hwitnessFinal⟩,
    ⟨hseedWitness.2.1, hseedWitness.2.2.trans hwitnessFinal⟩, hactual.mono hactualFinal⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators NNReal

theorem exists_preparedScalarFiniteSchedule_power_budget
    (s nStages inputPower : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ {nX : ℕ} {K : Type} [Fintype K]
        (degree : K → ℕ) (Bstruct extraLate : ℝ) (sourceU modelLog : K → ℝ),
        Fintype.card K ≤ nStages → (∀ k, degree k ≤ s) → (nX : ℝ) ≤ p →
        Bstruct ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        extraLate ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        (∀ k, sourceU k ∈ Set.Icc 0 ((p + 2) ^ inputPower)) →
        (∀ k, modelLog k ∈ Set.Icc 0 ((p + 2) ^ inputPower)) →
        let Cdetect := fun k => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
        PreparedEmptyLayerLocalScheduleBudget (G := Fin (scalarNativeDimension s))
          (max s 1) degree Cdetect nX (scalarNativeDimension s)
          Bstruct (scalarNativeDimension s : ℝ) 0 0 0 extraLate sourceU modelLog
          ((p + 2) ^ C) ∧
        preparedEmptyLayerLocalTailWidthLog (G := Fin (scalarNativeDimension s))
          (max s 1) degree Cdetect nX (scalarNativeDimension s)
          Bstruct (scalarNativeDimension s : ℝ) 0 0 sourceU modelLog ≤ (p + 2) ^ C := by
  let Cmax := ∑ d : Fin (s + 1), sampledSupportedSlicedDetectionConstant d.val Pdetect
  obtain ⟨Cbase, hCbase, hbase⟩ :=
    exists_preparedEmptyLayerLocalSchedule_budget (max s 1) nStages Cmax
  let input : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower + Polynomial.X +
    Polynomial.C (scalarNativeDimension s)
  let capPoly : Polynomial ℕ := (input + 2) ^ Cbase
  let bound : Polynomial ℕ :=
    Polynomial.C (⌈(probabilityProfileLipschitz : ℝ)⌉₊ + 12) + 4 * capPoly
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget bound
  refine ⟨C, hC, ?_⟩
  intro p hp nX K _ degree Bstruct extraLate sourceU modelLog
    hCard hdegree hnX hB hExtra hu hmodel Cdetect
  let P : ℝ := (p + 2) ^ inputPower + p + scalarNativeDimension s
  have ht : 0 ≤ (p + 2) ^ inputPower := by positivity
  have hd : (0 : ℝ) ≤ scalarNativeDimension s := Nat.cast_nonneg _
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have htP : (p + 2) ^ inputPower ≤ P := by dsimp only [P]; linarith
  have hpP : p ≤ P := by dsimp only [P]; linarith
  have hdP : (scalarNativeDimension s : ℝ) ≤ P := by dsimp only [P]; linarith
  have lift {x : ℝ} (hx : x ∈ Set.Icc 0 ((p + 2) ^ inputPower)) :
      x ∈ Set.Icc 0 P := ⟨hx.1, hx.2.trans htP⟩
  have hCdetect (k : K) : Cdetect k ≤ Cmax := by
    let d : Fin (s + 1) := ⟨degree k, Nat.lt_succ_of_le (hdegree k)⟩
    have hsum := Finset.single_le_sum
      (f := fun d : Fin (s + 1) => sampledSupportedSlicedDetectionConstant d.val Pdetect)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ d)
    exact hsum
  have hSchedule := hbase (G := Fin (scalarNativeDimension s)) degree Cdetect
    (nX := nX) (count := scalarNativeDimension s)
    (P := P) (Bstruct := Bstruct) (pnum := (scalarNativeDimension s : ℝ))
    (Qstride := 0) (Qσ := 0) (requestedCoarse := 0) (extraLate := extraLate)
    sourceU modelLog hCard (fun k => (hdegree k).trans (le_max_left s 1)) hCdetect
    hP (lift hB) ⟨hd, hdP⟩ ⟨le_rfl, hP⟩ ⟨le_rfl, hP⟩ ⟨le_rfl, hP⟩
    (lift hExtra) (fun k => lift (hu k)) (fun k => lift (hmodel k)) hdP
    (hnX.trans hpP) (by simpa only [Fintype.card_fin] using hdP)
  have hmajor : (⌈(probabilityProfileLipschitz : ℝ)⌉₊ : ℝ) + 12 +
      4 * (P + 2) ^ Cbase ≤ (p + 2) ^ C := by
    simpa [bound, capPoly, input, P, Polynomial.eval₂_pow] using hbound p hp
  have hcap0 : 0 ≤ (P + 2) ^ Cbase := by positivity
  have hceil0 : (0 : ℝ) ≤ ⌈(probabilityProfileLipschitz : ℝ)⌉₊ := Nat.cast_nonneg _
  have hcap : (P + 2) ^ Cbase ≤ (p + 2) ^ C := by
    linarith only [hmajor, hcap0, hceil0]
  refine ⟨hSchedule.mono hcap, ?_⟩
  have hwidth := hSchedule.tailWidthLog_le
  have hprofile := Nat.le_ceil (probabilityProfileLipschitz : ℝ)
  exact hwidth.trans (by linarith only [hmajor, hprofile, hcap0])

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

theorem exists_preparedScalarFiniteSchedule_two_stage_power_budget
    (s nStages inputPower : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ Cearly : ℕ, 2 ≤ Cearly ∧ ∀ latePower : ℕ,
      ∃ Clate : ℕ, 2 ≤ Clate ∧ ∀ {p : ℝ}, 0 ≤ p →
        ∀ {nX : ℕ} {K : Type} [Fintype K]
          (degree : K → ℕ) (Bstruct extraLate : ℝ) (sourceU modelLog : K → ℝ),
          Fintype.card K ≤ nStages → (∀ k, degree k ≤ s) → (nX : ℝ) ≤ p →
          Bstruct ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
          extraLate ∈ Set.Icc 0 ((p + 2) ^ latePower) →
          (∀ k, sourceU k ∈ Set.Icc 0 ((p + 2) ^ inputPower)) →
          (∀ k, modelLog k ∈ Set.Icc 0 ((p + 2) ^ inputPower)) →
          let Cdetect := fun k => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
          PreparedEmptyLayerLocalScheduleBudget (G := Fin (scalarNativeDimension s))
            (max s 1) degree Cdetect nX (scalarNativeDimension s)
            Bstruct (scalarNativeDimension s : ℝ) 0 0 0 0 sourceU modelLog
            ((p + 2) ^ Cearly) ∧
          preparedEmptyLayerLocalTailWidthLog (G := Fin (scalarNativeDimension s))
            (max s 1) degree Cdetect nX (scalarNativeDimension s)
            Bstruct (scalarNativeDimension s : ℝ) 0 0 sourceU modelLog ≤ (p + 2) ^ Cearly ∧
          PreparedEmptyLayerLocalScheduleBudget (G := Fin (scalarNativeDimension s))
            (max s 1) degree Cdetect nX (scalarNativeDimension s)
            Bstruct (scalarNativeDimension s : ℝ) 0 0 0 extraLate sourceU modelLog
            ((p + 2) ^ Clate) := by
  obtain ⟨Cearly, hCearly, hEarly⟩ :=
    exists_preparedScalarFiniteSchedule_power_budget s nStages inputPower Pdetect
  refine ⟨Cearly, hCearly, ?_⟩
  intro latePower
  obtain ⟨Clate, hClate, hLate⟩ :=
    exists_preparedScalarFiniteSchedule_power_budget s nStages (max inputPower latePower) Pdetect
  refine ⟨Clate, hClate, ?_⟩
  intro p hp nX K _ degree Bstruct extraLate sourceU modelLog
    hCard hdegree hnX hB hExtra hu hmodel Cdetect
  have hEarlyData := hEarly hp degree Bstruct 0 sourceU modelLog
    hCard hdegree hnX hB ⟨le_rfl, by positivity⟩ hu hmodel
  have hbase : 1 ≤ p + 2 := by linarith
  have hInput : (p + 2) ^ inputPower ≤ (p + 2) ^ max inputPower latePower :=
    pow_le_pow_right₀ hbase (le_max_left inputPower latePower)
  have hLatePower : (p + 2) ^ latePower ≤ (p + 2) ^ max inputPower latePower :=
    pow_le_pow_right₀ hbase (le_max_right inputPower latePower)
  have lift {x : ℝ} (hx : x ∈ Set.Icc 0 ((p + 2) ^ inputPower)) :
      x ∈ Set.Icc 0 ((p + 2) ^ max inputPower latePower) :=
    ⟨hx.1, hx.2.trans hInput⟩
  have hLateData := hLate hp degree Bstruct extraLate sourceU modelLog
    hCard hdegree hnX (lift hB) ⟨hExtra.1, hExtra.2.trans hLatePower⟩
    (fun k => lift (hu k)) (fun k => lift (hmodel k))
  exact ⟨hEarlyData.1, hEarlyData.2, hLateData.1⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

theorem exists_preparedFiniteNestedSourceLate_power_budget
    (m cutoff A Cdirect outerDepth innerDepth inputPower : ℕ)
    (constants : ℕ → ℕ) (hA : 2 ≤ A) (hcutoff : cutoff ≤ m) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (G : Type) [Fintype G] (count nX : ℕ)
      {Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse : ℝ},
      0 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct → (Fintype.card G : ℝ) ≤ Bstruct →
      Vlog ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Qσ ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Pmin ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      requestedCoarse ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
      let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
      let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k)
        (preparedFiniteForwardDetectorPolynomial cutoff)
      let u := fun k : K => preparedFiniteForwardPairedSourcePrecision A Cdirect constants
        (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k) gainLog stageLog
      let model := fun k : K => preparedFiniteForwardWork A constants
        (preparedFiniteNestedForwardAllDegreeStage k).val
        (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k)
      let Qw := 2 * Bstruct + 2 * Vlog + 5 * (gainLog + 8) + 24
      PreparedFiniteScheduleWitnessBudget (G := G) m degree Cdetect nX count
        Bstruct pnum Qstride Qσ Pmin Qw requestedCoarse u model ((Bstruct + 2) ^ C) := by
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
  let Cmax := ∑ d : Fin (m + 1), sampledSupportedSlicedDetectionConstant d.val
    (preparedFiniteForwardDetectorPolynomial cutoff)
  obtain ⟨Clocal, _, hlocal⟩ :=
    exists_candidateNestedForwardLocal_budget A Cdirect constants innerDepth outerDepth hA
  let inputPoly : Polynomial ℕ := 8 * Polynomial.X + (Polynomial.X + 2) ^ Clocal +
    3 * (Polynomial.X + 2) ^ inputPower + 64
  obtain ⟨Cin, _, hinput⟩ := exists_natPolynomial_fixed_power_budget inputPoly
  obtain ⟨C, hC, hcore⟩ := exists_preparedFiniteScheduleWitnessLate_power_budget
    m (Fintype.card K) Cmax Cin
  refine ⟨C, hC, ?_⟩
  intro G _ count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse
    hB hnum hstride hg hs hcount hnX hG hV hQσ hPmin hcoarse K' degree Cdetect u model Qw
  let localBound := (Bstruct + 2) ^ Clocal
  let primitiveBound := (Bstruct + 2) ^ inputPower
  let inputBound := (Bstruct + 2) ^ Cin
  have hl0 : 0 ≤ localBound := by dsimp only [localBound]; positivity
  have hp0 : 0 ≤ primitiveBound := by dsimp only [primitiveBound]; positivity
  have hbound : 8 * Bstruct + localBound + 3 * primitiveBound + 64 ≤ inputBound := by
    simpa [inputPoly, localBound, primitiveBound, inputBound, Polynomial.eval₂_pow] using hinput Bstruct hB
  have hBinput : Bstruct ≤ inputBound := by linarith only [hbound, hB, hl0, hp0]
  have hlocalInput : localBound ≤ inputBound := by linarith only [hbound, hB, hp0]
  have hprimitiveInput : primitiveBound ≤ inputBound := by linarith only [hbound, hB, hl0, hp0]
  have liftBase {x : ℝ} (hx : x ∈ Set.Icc 0 Bstruct) : x ∈ Set.Icc 0 inputBound :=
    ⟨hx.1, hx.2.trans hBinput⟩
  have liftPrimitive {x : ℝ} (hx : x ∈ Set.Icc 0 primitiveBound) : x ∈ Set.Icc 0 inputBound :=
    ⟨hx.1, hx.2.trans hprimitiveInput⟩
  have hQw : Qw ∈ Set.Icc 0 inputBound := by
    constructor
    · dsimp only [Qw]; have := hV.1; have := hg.1; positivity
    · dsimp only [Qw]
      linarith only [hbound, hV.2, hg.2, hB, hl0, hp0]
  have hstage (k : K') := hlocal hB hg hs k.1.val (Nat.le_of_lt_succ k.1.isLt)
    k.2.1.val (Nat.le_of_lt_succ k.2.1.isLt)
  have hu (k : K') : u k ∈ Set.Icc 0 inputBound := by
    have h := (hstage k).2.2.2.2.2 (preparedFiniteNestedForwardAllDegreeIsDirect k)
    exact ⟨h.1, h.2.trans hlocalInput⟩
  have hmodel (k : K') : model k ∈ Set.Icc 0 inputBound := by
    have h := (hstage k).2.2.1
    exact ⟨h.1, h.2.trans hlocalInput⟩
  have hdegree (k : K') : degree k ≤ m :=
    preparedFiniteNestedForwardAllDegreeDegree_le hcutoff k
  have hCdetect (k : K') : Cdetect k ≤ Cmax := by
    let d : Fin (m + 1) := ⟨degree k, Nat.lt_succ_of_le (hdegree k)⟩
    exact Finset.single_le_sum
      (f := fun d : Fin (m + 1) => sampledSupportedSlicedDetectionConstant d.val
        (preparedFiniteForwardDetectorPolynomial cutoff))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ d)
  exact hcore (G := G) degree Cdetect u model le_rfl hdegree hCdetect hB
    ⟨hB, hBinput⟩ (liftBase hnum) (liftBase hstride) (liftPrimitive hQσ)
    (liftPrimitive hPmin) hQw (liftPrimitive hcoarse) hu hmodel
    (hcount.trans hBinput) (hnX.trans hBinput) (hG.trans hBinput)

end Erdos3.VectorPolynomial

end

end OAI

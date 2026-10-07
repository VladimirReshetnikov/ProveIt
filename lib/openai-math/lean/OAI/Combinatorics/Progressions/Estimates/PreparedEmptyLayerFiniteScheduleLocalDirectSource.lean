import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedEmptyLayerFiniteScheduleLocalDirectSource
    {m s nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)]
    {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    (Vtail : Fin m → ℝ≥0) (τ : ℝ)
    (Q : Fin m → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {K : Type} [Fintype K] (degree : K → ℕ)
    (selection : ∀ k, Fin (degree k + 1) ↪ G)
    (hm : 0 < m) (hsm : s ≤ m) (hdegree : ∀ k, degree k ≤ s)
    (hcapacity : (s + 1) * (s + 3) ≤ Fintype.card G)
    (Bstruct Qstride Qσ requestedCoarse extraLate : ℝ)
    (sourceU modelLog sliceLog : K → ℝ)
    (hB : 0 ≤ Bstruct) (hnum : (Fintype.card G : ℝ) ≤ Bstruct)
    (hsourceU : ∀ k, 0 ≤ sourceU k) (hmodelLog : ∀ k, 0 ≤ modelLog k)
    (hsliceModel : ∀ k, sliceLog k ≤ modelLog k)
    (hcountModel : ∀ k, (Fintype.card G : ℝ) ≤ Real.exp (modelLog k))
    (hQstride : 0 ≤ Qstride) (hQσ : 0 ≤ Qσ) :
    let count := Fintype.card (LayerSamplerVariables G I n B)
    let pnum : ℝ := Fintype.card G
    let Cdetect := fun k => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun k => slicedDetectionGainLog (degree k) (Cdetect k)
      count (pDetect k) (pDetect k) (aDetect k)
    let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
      (detectionGain k + pDetect k + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
    let Prho := fun k => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
    let Ptail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun k => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
    let lengthLogs := fun k => allocatedAffineLengthLog m D Pscale (Prho k) (Pk k)
      (target k) (pDetect k + 2) (Tmod k)
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let localLate := fun k : K => preparedUniformDegreeDirectLate
      (Pmaster k) Pscale (Pphysical k) coarseTarget extraLate
    let Plate := ∑ k : K, localLate k
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      ∀ S : LayerSamplerScale (G := G) B U b R (fun _ => σ),
        (∀ k, Real.exp (lengthLogs k) ≤ S.value) →
        (S.value : ℝ) ≤ Real.exp extraLate →
        (∀ k, PreparedUniformDegreeDirectScalarBounds m (degree k) nX count (Cdetect k)
          Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
          (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
        (∀ k, PreparedUniformDegreeGeometryAt B U b S (degree k) (Cdetect k) nX
          Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (pDetect k) pRadius
          (aDetect k) (detectionGain k)) ∧
        (∀ k, PreparedScheduledDirectSourceAvailability
          (B := B) (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := selection k) (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) := by
  intro count pnum Cdetect R pRadius D pDetect aDetect detectionGain Pk Pphysical target E
    Prho Ptail Pscale Tmod lengthLogs Pmaster coarseTarget localLate Plate
  let : ∀ j, CompactSpace (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun j => latticeQuotient_compact _
  let ν := fun j => probabilityAddHaar (euclideanSubspace (U j) ⧸
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup)
  let : ∀ j, (ν j).IsAddLeftInvariant := fun j => probabilityAddHaar_invariant _
  let : ∀ j, IsProbabilityMeasure (ν j) := fun j => probabilityAddHaar_probability _
  let : CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U) :=
    coefficientTorus_compact_of_lattice U
  let : MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U) := borel _
  let : BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U) := ⟨rfl⟩
  let μ := probabilityAddHaar (CoefficientTorus (K := LayerSamplerVariables G I n B) U)
  let : μ.IsAddLeftInvariant := probabilityAddHaar_invariant _
  let : IsProbabilityMeasure μ := probabilityAddHaar_probability _
  have hcount : count = Fintype.card G := emptyLayerVariables_card B
  have hpnum : 0 ≤ pnum := Nat.cast_nonneg _
  have hvars : (count : ℝ) ≤ pnum := by simp only [hcount, pnum, le_refl]
  have hI (j) : (Fintype.card (I j) : ℝ) ≤ pnum := by
    simpa only [Fintype.card_eq_zero, Nat.cast_zero] using hpnum
  have hn (j) : (n j : ℝ) ≤ pnum := by
    have hnzero : n j = 0 := by
      have := Fintype.card_eq_zero (α := Fin (n j))
      simpa only [Fintype.card_fin] using this
    simpa only [hnzero, Nat.cast_zero] using hpnum
  have hblocks (k : K) (a : LayerSamplerAxis I n) :
      (boundedBooleanJetRows (Fin (degree k + 1)) (a.1.val + 1)).card ≤ Fintype.card (B a) := by
    exact Sum.elim isEmptyElim isEmptyElim a.2
  have hpDetect (k) : 0 ≤ pDetect k := by
    dsimp only [pDetect, allocatedModelTestLog]
    linarith only [hsourceU k, hmodelLog k]
  have haDetect (k) : 0 ≤ aDetect k := by
    dsimp only [aDetect]
    linarith only [hsourceU k, hmodelLog k]
  have hgain (k) : 0 ≤ detectionGain k :=
    slicedDetectionGainLog_nonneg (degree k) (Cdetect k) count
      (hpDetect k) (hpDetect k) (haDetect k)
  have hkernel (k) : 0 ≤ Pk k := by
    dsimp only [Pk]
    rw [scalarKernelLogarithmicBudget_eq]
    have := hgain k
    have := hpDetect k
    positivity
  have hphysical (k) : 0 ≤ Pphysical k := by
    dsimp only [Pphysical, preparedFiniteScheduleLocalPhysical]
    have := hkernel k
    positivity
  have htarget (k) : 0 ≤ target k := by
    have he := coefficientErrorSpatialLog_nonneg (hphysical k)
    dsimp only [target]
    linarith only [hgain k, he]
  have hgeometry := exists_preparedFiniteScheduleGeometryPrescribedScale m degree Cdetect B
    nX pDetect aDetect target hm (fun k => (hdegree k).trans hsm)
    hB ⟨hpnum, hnum⟩ hvars hI hn hblocks hpDetect haDetect hQstride htarget
  obtain ⟨hpRadius, hR, hD, hlogs, t, ht, hsamplers⟩ := hgeometry
  obtain ⟨hσ, hσone, hσt, hσexp, hσinv, hPscale, hDscale, hPkScale, hscales⟩ := hsamplers hQσ
  let σ := preparedUniformDegreeTolerance t Qσ
  refine ⟨(fun j => (hR j).1), σ, hσ, hpRadius.1, (fun j => (hR j).2),
    hσone, hσexp, hσinv, ?_⟩
  intro S hlength hS
  have hGeometryAll := hscales U b S hlength
  have hcoarse (k) : detectionGain k + 32 ≤ coarseTarget :=
    (Finset.single_le_sum (f := fun t : K => detectionGain t + 32)
      (fun t _ => by linarith only [hgain t])
      (Finset.mem_univ k)).trans (le_max_left _ _)
  have scalarLocal (k) := preparedFiniteScheduleLocalScalarBounds_explicit
    m (degree k) (Cdetect k) ((hdegree k).trans hsm) G nX count
    Bstruct D pRadius Qstride Pscale coarseTarget extraLate
    (sourceU k) (modelLog k) (sliceLog k) (Prho k)
    hB hD hpRadius.1 (hsourceU k) (hmodelLog k) hQstride (hlogs k).2.2.1
    (hsliceModel k) (by simpa only [hcount] using hcountModel k)
    (hPkScale k) (hcoarse k) (Plate := localLate k) le_rfl
  have hlocalLate0 (k) : 0 ≤ localLate k :=
    (scalarLocal k).master_nonneg.trans (scalarLocal k).late
  have hLate (k) : localLate k ≤ Plate :=
    Finset.single_le_sum (f := localLate)
      (fun t _ => hlocalLate0 t) (Finset.mem_univ k)
  have scalarAll (k) := (scalarLocal k).late_mono (hLate k)
  refine ⟨scalarAll, hGeometryAll, ?_⟩
  intro k
  exact preparedFiniteScheduleGeometryDirectSource
    (B := B) (U := U) (basis := b) (S := S)
    (hR := fun j => (hR j).1) (hσ := fun _ => hσ)
    (selection := selection k) (stride := stride) (N := N) (Pdetect := Pdetect)
    (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
    (Vtail := Vtail) (τ := τ) (Q := Q) (hb := hb) (o := o)
    (bW := bW) (ν := ν) (μ := μ)
    (Cdetect k) rfl ((hdegree k).trans hsm)
    Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
    (detectionGain k) (Pphysical k) coarseTarget pRadius (scalarAll k) (hGeometryAll k)
    (fun j => (hR j).2.1) (fun j => (hR j).2.2) (fun _ => hσone)
    (hS.trans (Real.exp_le_exp.mpr
      ((preparedUniformDegreeDirectLate_extra (Pmaster k) Pscale
        (Pphysical k) coarseTarget extraLate).trans (hLate k))))
    (fun j i => isEmptyElim i) (fun j i => isEmptyElim i)
    ((Nat.mul_le_mul (Nat.add_le_add_right (hdegree k) 1)
      (Nat.add_le_add_right (hdegree k) 3)).trans hcapacity)

end Erdos3.VectorPolynomial

end

end OAI

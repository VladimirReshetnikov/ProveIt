import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleCandidateDetection

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

def PreparedFiniteScheduleGeometryPrescribedScaleStatement (m : ℕ) {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
    {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {Bstruct pnum Qstride : ℝ} (nX : ℕ)
    (pDetect aDetect target : K → ℝ)
 : Prop :=
    let Aradius := Classical.choose (exists_preparedUniformEarlyRadius.{0,0,0,0} m)
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let gainLog := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables G I n B)) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K =>
      scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) G (gainLog s + pDetect s + 4)
    let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    pRadius ∈ Set.Icc 0 ((Bstruct + Bstruct + Aradius) ^ Aradius) ∧
    (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧ 0 ≤ D ∧
    (∀ s, 0 ≤ gainLog s ∧ 0 ≤ Pk s ∧ 0 ≤ Prho s ∧ 0 ≤ Ptail s) ∧
    ∃ t : K → ℝ,
      (∀ s, 0 < t s ∧ t s ≤ 1 ∧ (t s)⁻¹ ≤ Real.exp (Ptail s)) ∧
    ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := preparedUniformDegreeTolerance t Qσ
      let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
      let lengthLogs := fun s : K => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
        (target s) (pDetect s + 2) (Tmod s)
      0 < σ ∧ σ ≤ 1 ∧ (∀ s, σ ≤ t s) ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ 0 ≤ Pscale ∧ D ≤ Pscale ∧
      (∀ s, Pk s ≤ Pscale) ∧
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
      ∀ (S : LayerSamplerScale (G := G) B U basis R (fun _ => σ)),
        (∀ s : K, Real.exp (lengthLogs s) ≤ S.value) →
        ∀ s : K, PreparedUniformDegreeGeometryAt B U basis S (degree s) (Cdetect s) nX
          Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (gainLog s)

theorem exists_preparedFiniteScheduleGeometryPrescribedScale (m : ℕ) {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
    {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {Bstruct pnum Qstride : ℝ} (nX : ℕ)
    (pDetect aDetect target : K → ℝ)
    (hm : 0 < m) (hdegree : ∀ s, degree s ≤ m) (hB : 0 ≤ Bstruct) (hnum : pnum ∈ Set.Icc 0 Bstruct)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) (hn : ∀ j, (n j : ℝ) ≤ pnum)
    (hblocks : ∀ s : K, ∀ b : LayerSamplerAxis I n,
      (boundedBooleanJetRows (Fin ((degree s) + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b))
    (hp : ∀ s, 0 ≤ pDetect s) (ha : ∀ s, 0 ≤ aDetect s) (hQstride : 0 ≤ Qstride)
    (htarget : ∀ s, 0 ≤ target s) :
    PreparedFiniteScheduleGeometryPrescribedScaleStatement (G := G) m degree Cdetect B
      (Bstruct := Bstruct) (pnum := pnum) (Qstride := Qstride) nX pDetect aDetect target := by
  delta PreparedFiniteScheduleGeometryPrescribedScaleStatement
  intro Aradius pRadius R D gainLog Pk E Prho Ptail Tmod
  obtain ⟨hRadius, hR, hgeometry⟩ :=
    (Classical.choose_spec (exists_preparedUniformEarlyRadius.{0,0,0,0} m)).2 hB hB
  have hD : 0 ≤ D := (allocatedComparisonDimension_bounds m hnum.1).1
  have hD1 : 1 ≤ D := by
    have hd := (allocatedComparisonDimension_bounds m hnum.1).2.1
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    exact hm1.trans hd
  have hgain (s) : 0 ≤ gainLog s :=
    slicedDetectionGainLog_nonneg (degree s) (Cdetect s) _ (hp s) (hp s) (ha s)
  have hPk (s) : 0 ≤ Pk s := by
    change 0 ≤ scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) G (gainLog s + pDetect s + 4)
    rw [scalarKernelLogarithmicBudget_eq]
    have := hgain s
    have := hp s
    positivity
  have hcompare (s : K) : 0 ≤ Prho s ∧ 0 ≤ Ptail s ∧
      Nonempty (PreparedUniformDegreeComparison (G := G) B (degree s) D (target s)
        (Pk s) (Prho s) (Ptail s) (pDetect s)) :=
    exists_preparedUniformDegreeComparison B hm (hdegree s) hnum.1
      hvars hI hn (hblocks s) (hp s) (ha s) (htarget s) hQstride (Cdetect s) nX
  let data := fun s => Classical.choice (hcompare s).2.2
  let t := fun s => (data s).t
  have hTail (s) : 0 ≤ Ptail s := (hcompare s).2.1
  refine ⟨hRadius, hR, hD, fun s => ⟨hgain s, hPk s, (hcompare s).1, hTail s⟩,
    t, fun s => ⟨(data s).ht, (data s).htone, (data s).htinv⟩, ?_⟩
  intro Qσ hQσ σ Pscale lengthLogs
  obtain ⟨hσ, hσone, hσt, hσexp, hσinv, hPscale, hTailScale⟩ :=
    preparedUniformDegreeTolerance_bounds t Ptail (fun s => (data s).ht)
      (fun s => (data s).htone) hTail (fun s => (data s).htinv)
      hQσ (add_nonneg hD hRadius.1)
  have hsum : 0 ≤ ∑ s, Ptail s := Finset.sum_nonneg (fun s _ => hTail s)
  have hDscale : D ≤ Pscale := by
    change D ≤ D + pRadius + ∑ s, Ptail s + Qσ
    linarith only [hRadius.1, hsum, hQσ]
  have hRadiusScale : pRadius ≤ Pscale := by
    change pRadius ≤ D + pRadius + ∑ s, Ptail s + Qσ
    linarith only [hD, hsum, hQσ]
  have hPkScale (s) : Pk s ≤ Pscale :=
    (prepared_affineProfileToleranceEnvelope_kernel_bound hm canonicalSublevelCutoffLip
      canonicalTransitionLip hD1 (hPk s) (htarget s) (hp s)).trans (hTailScale s)
  refine ⟨hσ, hσone, hσt, hσexp, hσinv, hPscale, hDscale, hPkScale, ?_⟩
  intro J _ U basis S hlengths s
  exact preparedUniformDegreeGeometryAt_of_prescribedScale B U basis (Cdetect s) nX
    hm (hdegree s) hB hnum hvars hI hn (hp s) (ha s) hQstride (htarget s)
    (hcompare s).1 hPscale hDscale hRadiusScale (data s) S
    (fun _ => hσt s) (fun _ => hσinv) (hlengths s)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedFiniteScheduleDirectMaster {K : Type*} [Fintype K]
    (Pchart D pRadius Qstride Pphysical : ℝ)
    (u pModel Prho target gainLog : K → ℝ) : ℝ :=
  Pchart + D + pRadius + Qstride + Pphysical +
    ∑ k, (u k + pModel k + allocatedModelTestLog (u k) (pModel k) +
      Prho k + target k + gainLog k + 32)

noncomputable def preparedFiniteScheduleDirectCoarse {K : Type*} [Fintype K]
    (gainLog : K → ℝ) (requestedCoarse : ℝ) : ℝ :=
  max (∑ k, (gainLog k + 32)) requestedCoarse

theorem preparedFiniteScheduleDirectScalarBounds_explicit
    (m : ℕ) {K : Type*} [Fintype K] (degree Cdetect : K → ℕ)
    (hdegree : ∀ k, degree k ≤ m) (G : Type) [Fintype G]
    (nX count : ℕ) (Pchart D pRadius Qstride Pscale requestedCoarse extraLate : ℝ)
    (u pModel pSlice Prho : K → ℝ)
    (hchart : 0 ≤ Pchart) (hD : 0 ≤ D) (hradius : 0 ≤ pRadius)
    (hu : ∀ k, 0 ≤ u k) (hmodel : ∀ k, 0 ≤ pModel k) (hstride : 0 ≤ Qstride)
    (hrho : ∀ k, 0 ≤ Prho k) (hslice : ∀ k, pSlice k ≤ pModel k)
    (hcount : ∀ k, (count : ℝ) ≤ Real.exp (pModel k)) :
    let pDetect := fun k => allocatedModelTestLog (u k) (pModel k)
    let gainLog := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
      (pDetect k) (pDetect k) (2 * u k + 4 * pModel k + 7)
    let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
      (gainLog k + pDetect k + 4)
    let Pphysical : ℝ := ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + ∑ k, Pk k
    let target := fun k => gainLog k + 40 + coefficientErrorSpatialLog Pphysical
    let Pmaster := preparedFiniteScheduleDirectMaster Pchart D pRadius Qstride
      Pphysical u pModel Prho target gainLog
    let coarseTarget := preparedFiniteScheduleDirectCoarse gainLog requestedCoarse
    let Plate := preparedUniformDegreeDirectLate Pmaster Pscale Pphysical coarseTarget extraLate
    (∀ k, Pk k ≤ Pscale) → ∀ k,
      PreparedUniformDegreeDirectScalarBounds m (degree k) nX count (Cdetect k)
        Pchart Pscale D (target k) (Pk k) (Prho k) Qstride Pmaster Plate
        (gainLog k) Pphysical coarseTarget pRadius (u k) (pModel k) (pSlice k) := by
  intro pDetect gainLog Pk Pphysical target Pmaster coarseTarget Plate hkernelScale
  have hp (k) : 0 ≤ pDetect k := by
    dsimp only [pDetect, allocatedModelTestLog]
    have := hu k
    have := hmodel k
    positivity
  have ha (k) : 0 ≤ 2 * u k + 4 * pModel k + 7 := by
    have := hu k
    have := hmodel k
    positivity
  have hg (k) : 0 ≤ gainLog k :=
    slicedDetectionGainLog_nonneg (degree k) (Cdetect k) count (hp k) (hp k) (ha k)
  have hk (k) : 0 ≤ Pk k := by
    dsimp only [Pk]
    rw [scalarKernelLogarithmicBudget_eq]
    have := hg k
    have := hp k
    positivity
  have hkSum0 : 0 ≤ ∑ k, Pk k := Finset.sum_nonneg (fun k _ => hk k)
  have hkSum (k) : Pk k ≤ ∑ t, Pk t :=
    Finset.single_le_sum (fun t _ => hk t) (Finset.mem_univ k)
  have hphysEq : Pphysical = (m : ℝ) + 2 + nX + count + Qstride + ∑ k, Pk k := by
    simp only [Pphysical, Nat.cast_add, Nat.cast_ofNat]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hnX0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg nX
  have hcount0 : (0 : ℝ) ≤ count := Nat.cast_nonneg count
  have hphysical0 : 0 ≤ Pphysical := by
    linarith only [hphysEq, hm0, hnX0, hcount0, hstride, hkSum0]
  have hkernelPhysical (k) : Pk k ≤ Pphysical := by
    linarith only [hphysEq, hm0, hnX0, hcount0, hstride, hkSum k]
  have herror0 := coefficientErrorSpatialLog_nonneg hphysical0
  have ht (k) : 0 ≤ target k := by
    dsimp only [target]
    have := hg k
    positivity
  let total := ∑ k, (u k + pModel k + pDetect k + Prho k + target k + gainLog k + 32)
  have hentry (k) : 0 ≤ u k + pModel k + pDetect k + Prho k + target k + gainLog k + 32 := by
    have := hu k
    have := hmodel k
    have := hp k
    have := hrho k
    have := ht k
    have := hg k
    positivity
  have htotal0 : 0 ≤ total := Finset.sum_nonneg (fun k _ => hentry k)
  have htotal (k) : u k + pModel k + pDetect k + Prho k + target k + gainLog k + 32 ≤ total :=
    Finset.single_le_sum (fun k _ => hentry k) (Finset.mem_univ k)
  have hmasterEq : Pmaster = Pchart + D + pRadius + Qstride + Pphysical + total := rfl
  have hmaster0 : 0 ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hstride, hphysical0, htotal0]
  have hphysicalMaster : Pphysical ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hstride, htotal0]
  have htotalMaster : total ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hstride, hphysical0]
  have hlate : Pmaster ≤ Plate := le_max_left _ _
  have hscaleLate : Pscale ≤ Plate := (le_max_left _ _).trans (le_max_right _ _)
  have hcoarseLate : coarseTarget ≤ Plate :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hxiLate : 2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4
      ≤ Plate :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  intro k
  have hsmReal : (degree k : ℝ) ≤ m := by exact_mod_cast hdegree k
  have hlocalMaster := (htotal k).trans htotalMaster
  have hgainEntry (t : K) : (0 : ℝ) ≤ gainLog t + 32 := by
    have := hg t
    positivity
  have hcoarseSum : gainLog k + 32 ≤ ∑ t, (gainLog t + 32) :=
    Finset.single_le_sum (fun t _ => hgainEntry t) (Finset.mem_univ k)
  refine {
    master_nonneg := hmaster0
    late := hlate
    chart_master := ?_
    dimension_master := ?_
    radius_master := ?_
    scale_late := hscaleLate
    kernel_scale := hkernelScale k
    kernel_master := ⟨hk k, (hkernelPhysical k).trans hphysicalMaster⟩
    stride_master := ⟨hstride, ?_⟩
    detect_master := ⟨hp k, ?_⟩
    ambient_master := le_trans ?_ hphysicalMaster
    u_master := ⟨hu k, ?_⟩
    model_master := ⟨hmodel k, ?_⟩
    slice_model := hslice k
    count_model := hcount k
    rho_master := ⟨hrho k, ?_⟩
    target_master := ⟨ht k, ?_⟩
    gain_master := ⟨hg k, ?_⟩
    coarse_master := ?_
    coarse_lower := hcoarseSum.trans (le_max_left _ _)
    coarse_late := hcoarseLate
    physical_master := ⟨hphysical0, hphysicalMaster⟩
    degree_physical := ?_
    detector_physical := ?_
    variables_physical := ?_
    ambient_physical := ?_
    kernel_physical := hkernelPhysical k
    stride_physical := ?_
    gain_log := le_rfl
    precision := ?_
    xi_late := hxiLate }
  · linarith only [hmasterEq, hD, hradius, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hradius, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hD, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hD, hradius, hphysical0, htotal0]
  · linarith only [hlocalMaster, hu k, hmodel k, hrho k, ht k, hg k]
  · linarith only [hphysEq, hm0, hcount0, hstride, hkSum0]
  · linarith only [hlocalMaster, hmodel k, hp k, hrho k, ht k, hg k]
  · linarith only [hlocalMaster, hu k, hp k, hrho k, ht k, hg k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, ht k, hg k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, hrho k, hg k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, hrho k, ht k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, hrho k, ht k]
  · simp only [Nat.cast_add, Nat.cast_one]
    linarith only [hphysEq, hnX0, hcount0, hstride, hkSum0]
  · simp only [Nat.cast_add, Nat.cast_ofNat]
    linarith only [hphysEq, hsmReal, hnX0, hcount0, hstride, hkSum0]
  · linarith only [hphysEq, hm0, hnX0, hstride, hkSum0]
  · linarith only [hphysEq, hm0, hcount0, hstride, hkSum0]
  · linarith only [hphysEq, hm0, hnX0, hcount0, hkSum0]
  · dsimp only [target]
    linarith only

theorem preparedFiniteScheduleDirectCoarse_requested {K : Type*} [Fintype K]
    (gainLog : K → ℝ) (requestedCoarse : ℝ) :
    requestedCoarse ≤ preparedFiniteScheduleDirectCoarse gainLog requestedCoarse :=
  le_max_right _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedEmptyLayerFiniteScheduleDirectSource
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
    let Pphysical : ℝ := ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + ∑ k, Pk k
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog Pphysical
    let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
    let Prho := fun k => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
    let Ptail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun k => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
    let lengthLogs := fun k => allocatedAffineLengthLog m D Pscale (Prho k) (Pk k)
      (target k) (pDetect k + 2) (Tmod k)
    let Pmaster := preparedFiniteScheduleDirectMaster Bstruct D pRadius Qstride
      Pphysical sourceU modelLog Prho target detectionGain
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := preparedUniformDegreeDirectLate Pmaster Pscale Pphysical coarseTarget extraLate
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      ∀ S : LayerSamplerScale (G := G) B U b R (fun _ => σ),
        (∀ k, Real.exp (lengthLogs k) ≤ S.value) →
        (S.value : ℝ) ≤ Real.exp extraLate →
        (∀ k, PreparedUniformDegreeDirectScalarBounds m (degree k) nX count (Cdetect k)
          Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride Pmaster Plate
          (detectionGain k) Pphysical coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
        (∀ k, PreparedScheduledDirectSourceAvailability
          (B := B) (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := selection k) (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride Pmaster Plate (detectionGain k) Pphysical coarseTarget) := by
  intro count pnum Cdetect R pRadius D pDetect aDetect detectionGain Pk Pphysical target E
    Prho Ptail Pscale Tmod lengthLogs Pmaster coarseTarget Plate
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
  have hkernelSum : 0 ≤ ∑ k, Pk k := Finset.sum_nonneg (fun k _ => hkernel k)
  have hphysical : 0 ≤ Pphysical := by
    dsimp only [Pphysical]
    positivity
  have htarget (k) : 0 ≤ target k := by
    have he := coefficientErrorSpatialLog_nonneg hphysical
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
  have scalarAll := preparedFiniteScheduleDirectScalarBounds_explicit m degree Cdetect
    (fun k => (hdegree k).trans hsm) G nX count Bstruct D pRadius Qstride Pscale
    requestedCoarse extraLate sourceU modelLog sliceLog Prho hB hD hpRadius.1
    hsourceU hmodelLog hQstride (fun k => (hlogs k).2.2.1) hsliceModel
    (fun k => by simpa only [hcount] using hcountModel k) hPkScale
  refine ⟨scalarAll, ?_⟩
  intro k
  exact preparedFiniteScheduleGeometryDirectSource
    (B := B) (U := U) (basis := b) (S := S)
    (hR := fun j => (hR j).1) (hσ := fun _ => hσ)
    (selection := selection k) (stride := stride) (N := N) (Pdetect := Pdetect)
    (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
    (Vtail := Vtail) (τ := τ) (Q := Q) (hb := hb) (o := o)
    (bW := bW) (ν := ν) (μ := μ)
    (Cdetect k) rfl ((hdegree k).trans hsm)
    Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride Pmaster Plate
    (detectionGain k) Pphysical coarseTarget pRadius (scalarAll k) (hGeometryAll k)
    (fun j => (hR j).2.1) (fun j => (hR j).2.2) (fun _ => hσone)
    (hS.trans (Real.exp_le_exp.mpr
      (preparedUniformDegreeDirectLate_extra Pmaster Pscale Pphysical coarseTarget extraLate)))
    (fun j i => isEmptyElim i) (fun j i => isEmptyElim i)
    ((Nat.mul_le_mul (Nat.add_le_add_right (hdegree k) 1)
      (Nat.add_le_add_right (hdegree k) 3)).trans hcapacity)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators

abbrev PreparedFiniteForwardSlot (depth : ℕ) := Fin (depth + 1) × Bool

def preparedFiniteForwardSlotDegree {depth : ℕ} (k : PreparedFiniteForwardSlot depth) : ℕ :=
  if k.2 then k.1.val else 0

def preparedFiniteForwardModelSlot {depth : ℕ} (n : Fin (depth + 1)) :
    PreparedFiniteForwardSlot depth := (n, false)

def preparedFiniteForwardDetectionSlot {depth : ℕ} (n : Fin (depth + 1)) :
    PreparedFiniteForwardSlot depth := (n, true)

@[simp] theorem preparedFiniteForwardModelSlot_degree {depth : ℕ} (n : Fin (depth + 1)) :
    preparedFiniteForwardSlotDegree (preparedFiniteForwardModelSlot n) = 0 := rfl

@[simp] theorem preparedFiniteForwardDetectionSlot_degree {depth : ℕ} (n : Fin (depth + 1)) :
    preparedFiniteForwardSlotDegree (preparedFiniteForwardDetectionSlot n) = n.val := rfl

theorem preparedFiniteForwardSlot_degree_le {depth m : ℕ} (hdepth : depth ≤ m)
    (k : PreparedFiniteForwardSlot depth) : preparedFiniteForwardSlotDegree k ≤ m := by
  unfold preparedFiniteForwardSlotDegree
  split
  · exact (Nat.le_of_lt_succ k.1.isLt).trans hdepth
  · exact Nat.zero_le _

@[simp] theorem preparedFiniteForwardSlot_card (depth : ℕ) :
    Fintype.card (PreparedFiniteForwardSlot depth) = 2 * (depth + 1) := by
  simp [PreparedFiniteForwardSlot, Nat.mul_comm]

theorem preparedFiniteForwardSourceSlots_inputs
    (depth m A count : ℕ) (stageCountConstant : ℕ → ℕ)
    {x gainLog stageLog : ℝ} (hdepth : depth ≤ m) (hA : 2 ≤ A)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (hcount : (count : ℝ) ≤ x) :
    let sourceU := fun k : PreparedFiniteForwardSlot depth =>
      preparedFiniteForwardSourcePrecision A stageCountConstant k.1.val x gainLog stageLog
    let modelLog := fun k : PreparedFiniteForwardSlot depth =>
      preparedFiniteForwardWork A stageCountConstant k.1.val x
    let sliceLog := fun k : PreparedFiniteForwardSlot depth =>
      preparedFiniteForwardParameter A stageCountConstant k.1.val x
    (∀ k : PreparedFiniteForwardSlot depth, preparedFiniteForwardSlotDegree k ≤ m) ∧
    (∀ k, 0 ≤ sourceU k) ∧ (∀ k, 0 ≤ modelLog k) ∧
    (∀ k, sliceLog k ≤ modelLog k) ∧
    (∀ k, (count : ℝ) ≤ Real.exp (modelLog k)) ∧
    ∀ n : Fin (depth + 1),
      let k := preparedFiniteForwardModelSlot n
      sourceU k = preparedFiniteForwardModelPrecision A stageCountConstant n.val x gainLog stageLog +
        2 * modelLog k + 1 ∧ sliceLog k * count ≤ modelLog k := by
  intro sourceU modelLog sliceLog
  have hscalar (k : PreparedFiniteForwardSlot depth) :=
    preparedFiniteForward_model_scalar_bounds A stageCountConstant k.1.val count hA hx hcount
  have hprecision (k : PreparedFiniteForwardSlot depth) :=
    preparedFiniteForward_model_precision_bounds A stageCountConstant k.1.val hx hgain hstage
  exact ⟨preparedFiniteForwardSlot_degree_le hdepth,
    fun k => (hprecision k).2.1, fun k => (hscalar k).1,
    fun k => (hscalar k).2.1, fun k => (hscalar k).2.2.1,
    fun n => ⟨rfl, (hscalar (preparedFiniteForwardModelSlot n)).2.2.2⟩⟩

theorem exists_preparedFiniteForwardSourceSlots_budget
    (depth A : ℕ) (stageCountConstant : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (x gainLog stageLog : ℝ),
      0 ≤ x → gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      ∀ k : PreparedFiniteForwardSlot depth,
        preparedFiniteForwardSourcePrecision A stageCountConstant k.1.val x gainLog stageLog ∈
          Set.Icc 0 ((x + C) ^ C) ∧
        preparedFiniteForwardWork A stageCountConstant k.1.val x ∈ Set.Icc 0 ((x + C) ^ C) ∧
        preparedFiniteForwardParameter A stageCountConstant k.1.val x ∈ Set.Icc 0 ((x + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedFiniteForwardStage_budget depth A stageCountConstant
  refine ⟨C, hC, ?_⟩
  intro x gainLog stageLog hx hg hs k
  obtain ⟨hp, hw, _hcap, _hcount, _hbranch, _hcum, _hprefix, _hu, hsource⟩ :=
    hbound x gainLog stageLog hx hg hs k.1.val (Nat.le_of_lt_succ k.1.isLt)
  exact ⟨hsource, hw, hp⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedFiniteScheduleLocalPhysical
    (m nX count : ℕ) (Qstride Pk : ℝ) : ℝ :=
  ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + Pk

noncomputable def preparedFiniteScheduleLocalMaster
    (Pchart D pRadius Qstride Pphysical u pModel Prho target gainLog : ℝ) : ℝ :=
  Pchart + D + pRadius + Qstride + Pphysical +
    (u + pModel + allocatedModelTestLog u pModel + Prho + target + gainLog + 32)

theorem PreparedUniformDegreeDirectScalarBounds.late_mono
    {m s nX nVars Cdetect : ℕ}
    {Pchart Pscale D target Pk Prho Qstride Pmaster Plate Plate' pGain Pphysical
      coarseTarget pRadius u pModel pSlice : ℝ}
    (h : PreparedUniformDegreeDirectScalarBounds m s nX nVars Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical
      coarseTarget pRadius u pModel pSlice)
    (hLate : Plate ≤ Plate') :
    PreparedUniformDegreeDirectScalarBounds m s nX nVars Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate' pGain Pphysical
      coarseTarget pRadius u pModel pSlice := by
  exact { h with
    late := h.late.trans hLate
    scale_late := h.scale_late.trans hLate
    coarse_late := h.coarse_late.trans hLate
    xi_late := h.xi_late.trans hLate }

theorem preparedFiniteScheduleLocalScalarBounds_explicit
    (m degree Cdetect : ℕ) (hdegree : degree ≤ m) (G : Type) [Fintype G]
    (nX count : ℕ) (Pchart D pRadius Qstride Pscale coarseTarget extraLate : ℝ)
    (u pModel pSlice Prho : ℝ)
    (hchart : 0 ≤ Pchart) (hD : 0 ≤ D) (hradius : 0 ≤ pRadius)
    (hu : 0 ≤ u) (hmodel : 0 ≤ pModel) (hstride : 0 ≤ Qstride)
    (hrho : 0 ≤ Prho) (hslice : pSlice ≤ pModel)
    (hcount : (count : ℝ) ≤ Real.exp pModel) :
    let pDetect := allocatedModelTestLog u pModel
    let gainLog := slicedDetectionGainLog degree Cdetect count
      pDetect pDetect (2 * u + 4 * pModel + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
      (gainLog + pDetect + 4)
    let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
    let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
    let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
      Pphysical u pModel Prho target gainLog
    let localLate := preparedUniformDegreeDirectLate Pmaster Pscale Pphysical
      coarseTarget extraLate
    Pk ≤ Pscale → gainLog + 32 ≤ coarseTarget →
    ∀ {Plate : ℝ}, localLate ≤ Plate →
      PreparedUniformDegreeDirectScalarBounds m degree nX count Cdetect
        Pchart Pscale D target Pk Prho Qstride Pmaster Plate gainLog
        Pphysical coarseTarget pRadius u pModel pSlice := by
  intro pDetect gainLog Pk Pphysical target Pmaster localLate hkernel hcoarse Plate hLate
  have h := preparedFiniteScheduleDirectScalarBounds_explicit
    m (fun _ : Unit => degree) (fun _ : Unit => Cdetect) (fun _ => hdegree) G
    nX count Pchart D pRadius Qstride Pscale coarseTarget extraLate
    (fun _ => u) (fun _ => pModel) (fun _ => pSlice) (fun _ => Prho)
    hchart hD hradius (fun _ => hu) (fun _ => hmodel) hstride
    (fun _ => hrho) (fun _ => hslice) (fun _ => hcount)
    (fun _ => hkernel) ()
  have hlocal : PreparedUniformDegreeDirectScalarBounds m degree nX count Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster localLate gainLog
      Pphysical coarseTarget pRadius u pModel pSlice := by
    simpa only [preparedFiniteScheduleDirectMaster, preparedFiniteScheduleDirectCoarse,
      Finset.univ_unique, Finset.sum_singleton, max_eq_right hcoarse,
      Pmaster, Pphysical, target, localLate, gainLog, pDetect, Pk,
      preparedFiniteScheduleLocalPhysical, preparedFiniteScheduleLocalMaster] using h
  exact hlocal.late_mono hLate

end Erdos3.VectorPolynomial

end

end OAI

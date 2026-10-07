import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction
import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleModelAttachment
import OAI.Combinatorics.Progressions.Polynomial.PreparedFiniteForwardDegreeModelAttachment
import OAI.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeProductiveSource

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

private theorem finiteSchedule_affineLength_density_fin
    (m nX : ℕ) (D P Prho Pk target p Qstride : ℝ) :
    Real.exp (allocatedAffineLengthLog m D P Prho Pk target (p + 1)
      (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤
    Real.exp (allocatedAffineLengthLog m D P Prho Pk target (p + 2)
      (((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride)) := by
  simp only [Fintype.card_fin]
  exact Real.exp_le_exp.mpr (allocatedAffineLengthLog_prepared_density m D P Prho Pk target p _)

private theorem finiteSchedule_comparison_eta (target cost : ℝ) :
    Real.exp (-(target + cost + 5)) ≤ Real.exp (-(target + 1 + cost + 4)) := by
  apply Real.exp_le_exp.mpr
  linarith only

def PreparedFiniteScheduleGeometryStatement (m : ℕ) {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
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
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ},
        1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
      let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
      ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
        Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
        (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
          8 * (probabilityProfileLipschitz : ℝ) * W ≤
            (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
              ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
        ∀ s : K, PreparedUniformDegreeGeometryAt B U basis S (degree s) (Cdetect s) nX
          Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (gainLog s)

theorem exists_preparedFiniteScheduleGeometry (m : ℕ) {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
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
    PreparedFiniteScheduleGeometryStatement (G := G) m degree Cdetect B
      (Bstruct := Bstruct) (pnum := pnum) (Qstride := Qstride) nX pDetect aDetect target := by
  delta PreparedFiniteScheduleGeometryStatement
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
  have hdimensions (s : K) : AllocatedComparisonDimensions (G := G) B
      (Fin ((degree s) + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin ((degree s) + 1)) (j.val + 1) : Type)) D :=
    allocatedComparisonDimensions_of_primitive B
      (fun j => (Subtype.val : boundedBooleanJetRows (Fin ((degree s) + 1)) (j.val + 1) → Finset (Fin ((degree s) + 1))))
      (by simpa only [Fintype.card_fin] using Nat.succ_le_succ (hdegree s))
      (fun _ => Subtype.val_injective) hnum.1 hvars hI hn
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
  have hF (s : K) : 0 ≤ pDetect s + 2 := by linarith only [hp s]
  have hTmod (s) : 0 ≤ Tmod s :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hPk s))
      (mul_nonneg (Nat.cast_nonneg _) hQstride)
  have hLengths (s) : 0 ≤ lengthLogs s :=
    (allocatedAffineLengthLog_bounds m hD hPscale (hcompare s).1 (hPk s)
      (htarget s) (hF s) (hTmod s)).2.2.1
  refine ⟨hσ, hσone, hσt, hσexp, hσinv, hPscale, hDscale, hPkScale, ?_⟩
  intro Lmin W Qw Pmin hW hQw hWexp hPmin hLmin J _ U basis Pseed
  have hRi (j) : (R j)⁻¹ ≤ Real.exp Pscale :=
    (hR j).2.2.trans (Real.exp_le_exp.mpr hRadiusScale)
  have hdimZero : AllocatedComparisonDimensions (G := G) B (Fin 1)
      (fun j : Fin m => (boundedBooleanJetRows (Fin 1) (j.val + 1) : Type)) D :=
    allocatedComparisonDimensions_of_primitive B
      (fun j => (Subtype.val : boundedBooleanJetRows (Fin 1) (j.val + 1) → Finset (Fin 1)))
      (by simp) (fun _ => Subtype.val_injective) hnum.1 hvars hI hn
  obtain ⟨S, hlengths, hfloor, hS, hwidth⟩ :=
    exists_preparedUniformDegreeSampler B U basis R (fun _ => σ) lengthLogs
      hdimZero hDscale (fun j => (hR j).1) (fun _ => hσ)
      hRi (fun _ => hσinv) hLengths hPmin hLmin hW hQw hWexp
  refine ⟨S, hfloor, hS, hwidth, ?_⟩
  intro s
  let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin ((degree s) + 1)) (j.val + 1)
  let : ∀ j : Fin m, Nonempty (rowSets j) := fun j =>
    ⟨⟨∅, (mem_boundedBooleanJetRows (j.val + 1) ∅).mpr (by simp)⟩⟩
  obtain ⟨hrone, _, hT, hsource, hradius, hbudgets⟩ :=
    hgeometry (G := G) B rowSets
      (by simpa only [Fintype.card_fin] using Nat.succ_le_succ (hdegree s))
      (hvars.trans hnum.2) (fun j => (hI j).trans hnum.2) (fun j => (hn j).trans hnum.2)
  have hcount (j : Fin m) : (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp Pscale :=
    ((add_le_add ((hdimensions s).coefficients j) (le_refl (1 : ℝ))).trans
      (Real.add_one_le_exp D)).trans (Real.exp_le_exp.mpr hDscale)
  refine ⟨?_, ?_⟩
  · refine allocatedEarlyNativeSourceGeometryGeneral_of_fields B U basis S
      Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) (Real.toNNReal (Real.exp pRadius))
      hPscale (fun j => (hR j).2.1.trans (Real.one_le_exp hPscale))
      hRi (fun _ => hσinv) hcount (hdimensions s) (hPk s) (hcompare s).1 (htarget s) ?_
      (Real.exp (-(E s))) (Real.exp_pos _).le ?_ (data s).ρ (data s).t (data s).htone
      ((data s).hs)
      (data s).hρ (data s).hρ1 (data s).hρlog (fun _ => hσt s)
      (allocatedIdealCoverSupport (G := G) B rowSets) hT hsource
      (allocatedProductIdealSiteRadius (G := G) B rowSets) hrone hradius hbudgets
      (fun j => (hR j).2.2.trans (Real.le_coe_toNNReal _))
    · exact (finiteSchedule_affineLength_density_fin m nX D Pscale (Prho s) (Pk s)
        (target s) (pDetect s) Qstride).trans (hlengths s)
    · exact finiteSchedule_comparison_eta (target s) (D * ((m * 2 ^ (m + 1) : ℕ) * Pk s))
  · intro α hα gain
    have hcutoff := slicedDetection_kernel_cutoff_bound (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables G I n B)) G (hp s) (hp s) (ha s) hα
    exact ⟨slicedDetectionGain_lower (degree s) (Cdetect s) _ hα, hcutoff,
      allocatedAffineLength_kernel_ready hm hD hPscale (hcompare s).1 (hPk s)
        (htarget s) (hF s) (hTmod s) hcutoff (hlengths s)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedFiniteScheduleLocalProductiveSource
    {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
    (U : ∀ j, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    (Vtail : Fin m → ℝ≥0)

    (Q : Fin m → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

    {K : Type} [Fintype K] (degree Cdetect : K → ℕ) (kModel : K)
    (hdegree : ∀ k, degree k ≤ m) (hdegreeZero : degree kModel = 0)
    (hCzero : Cdetect kModel = sampledSupportedSlicedDetectionConstant 0 Pdetect)
    (Bstruct Qstride u p forecastCap : ℝ)
    (sourceU modelLog sliceLog : K → ℝ)
    (hModelSource : sourceU kModel = u + 2 * p + 1)
    (Qσ Qw Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < m) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hsourceU : ∀ k, 0 ≤ sourceU k) (hmodelLog : ∀ k, 0 ≤ modelLog k)
    (hsliceModel : ∀ k, sliceLog k ≤ modelLog k)
    (hcountModel : ∀ k, (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤ Real.exp (modelLog k))
    (hQstride : 0 ≤ Qstride)
    (hQσ : 0 ≤ Qσ) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct) :
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical m nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount m (nX + m * M)) * (nX + m * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    pnum ≤ Bstruct →
    W ≤ Real.exp Qw →
    sliceLog kModel * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) ≤ p →
    (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j)) ≤ Real.exp p →
    0 ≤ forecastCap → forecastCap ≤ Real.exp p →
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) («I» := (PreparedSamplerContinuous prep)) («n» := (preparedSamplerTransverse prep)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds m (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
          (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
          (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, Cdetect k = sampledSupportedSlicedDetectionConstant (degree k) Pdetect →
        PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, degree k = 0 →
        Cdetect k = sampledSupportedSlicedDetectionConstant 0 Pdetect →
        PreparedScheduledModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, Cdetect k = sampledSupportedSlicedDetectionConstant (degree k) Pdetect →
        PreparedScheduledDegreeModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := m) (nX := nX) (M := M) (prep := prep) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood := by
  intro pnum R pRadius D pDetect aDetect detectionGain Pk Pphysical target E Prho Ptail Pscale Tmod
    lengthLogs Pseed W Pmaster coarseTarget Plate τ hnum hWexp
    hSliceLog hCtail hForecastCap hForecastCapP
  have hpnum : 0 ≤ pnum := Nat.cast_nonneg _
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions prep (modularInitialBlockCount m (nX + m * M)) hCoord
  have hblocks (s : K) (a : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)) :
      (boundedBooleanJetRows (Fin (degree s + 1)) (a.1.val + 1)).card ≤ Fintype.card ((EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) a) := by
    calc
      _ = Fintype.card (BoundedBooleanJet (Fin (degree s + 1)) (a.1.val + 1)) :=
        (Fintype.card_coe _).symm.trans (Fintype.card_congr (boundedBooleanJetRowsEquiv _ _))
      _ ≤ _ := enlargedPreparedCommonSamplerBlock_jets prep (modularInitialBlockCount m (nX + m * M)) (degree s) (hdegree s) a
  have hpDetect (k) : 0 ≤ pDetect k := by
    dsimp only [pDetect, allocatedModelTestLog]
    linarith only [hsourceU k, hmodelLog k]
  have haDetect (k) : 0 ≤ aDetect k := by
    dsimp only [aDetect]
    linarith only [hsourceU k, hmodelLog k]
  have hgainDetect (k) : 0 ≤ detectionGain k :=
    slicedDetectionGainLog_nonneg (degree k) (Cdetect k) _ (hpDetect k) (hpDetect k) (haDetect k)
  have hkernel (k) : 0 ≤ Pk k := by
    dsimp only [Pk]
    rw [scalarKernelLogarithmicBudget_eq]
    have := hgainDetect k
    have := hpDetect k
    positivity
  have hphysical (k) : 0 ≤ Pphysical k := by
    dsimp only [Pphysical, preparedFiniteScheduleLocalPhysical]
    have := hkernel k
    positivity
  have hphysicalX (k) : (nX : ℝ) ≤ Pphysical k := by
    dsimp only [Pphysical, preparedFiniteScheduleLocalPhysical]
    have hcount : (0 : ℝ) ≤ Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) := Nat.cast_nonneg _
    have hm2 : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith only [hcount, hm2, hkernel k, hQstride]
  have htarget (k) : 0 ≤ target k := by
    have he := coefficientErrorSpatialLog_nonneg (hphysical k)
    dsimp only [target]
    linarith only [hgainDetect k, he]
  have hactual := exists_preparedFiniteScheduleGeometry m degree Cdetect (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) nX pDetect aDetect target
    hm hdegree hB ⟨hpnum, hnum⟩ (Nat.cast_le.mpr hvars) (fun j => Nat.cast_le.mpr (hI j))
    (fun j => Nat.cast_le.mpr (hn j)) hblocks hpDetect haDetect hQstride htarget
  obtain ⟨hpRadius, hR, hD, hlogs, t, ht, hsamplers⟩ := hactual
  obtain ⟨hσ, hσone, hσt, hσexp, hσinv, hPscale, hDscale, hPkScale, hscales⟩ := hsamplers hQσ
  have hW : 1 ≤ W := (physicalBadProductGap_budget _
    (show 0 ≤ gainLog + 8 by linarith only [hg]) hVlog Qgood hQgood hQexp).1
  obtain ⟨S, hFloor, hS, hgap, hGeometryAll⟩ := hscales Lmin hW hQw hWexp hPmin hLmin U b
  let σ := preparedUniformDegreeTolerance t Qσ
  have hF (s) : 0 ≤ pDetect s + 2 := by linarith only [hpDetect s]
  have hTmod (s) : 0 ≤ Tmod s :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hlogs s).2.1)
      (mul_nonneg (Nat.cast_nonneg _) hQstride)
  have hLengths (s) : 0 ≤ lengthLogs s :=
    (allocatedAffineLengthLog_bounds m hD hPscale (hlogs s).2.2.1 (hlogs s).2.1
      (htarget s) (hF s) (hTmod s)).2.2.1
  have hPseed : 0 ≤ Pseed := allocatedScaleLog_nonneg
    (add_nonneg (add_nonneg (add_nonneg hPscale (Finset.sum_nonneg (fun s _ => hLengths s))) hPmin)
      (by norm_num))
  have hmaster (k) : 0 ≤ Pmaster k := by
    dsimp only [Pmaster, preparedFiniteScheduleLocalMaster]
    have hr := (hlogs k).2.2.1
    have ht := htarget k
    have hph := hphysical k
    have hu := hsourceU k
    have hm := hmodelLog k
    have hd := hpDetect k
    have hg := hgainDetect k
    change 0 ≤ Bstruct + D + pRadius + Qstride + Pphysical k +
      (sourceU k + modelLog k + pDetect k + Prho k + target k + detectionGain k + 32)
    linarith only [hB, hD, hpRadius.1, hQstride, hr, ht, hph, hu, hm, hd, hg]
  have hLate (k) : preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw) ≤ Plate :=
    Finset.single_le_sum
      (f := fun t : K => preparedUniformDegreeDirectLate (Pmaster t) Pscale
        (Pphysical t) coarseTarget (allocatedWitnessScaleLog Pseed Qw))
      (fun t _ => (hmaster t).trans (le_max_left _ _)) (Finset.mem_univ k)
  have hcoarse (k) : detectionGain k + 32 ≤ coarseTarget := by
    exact (Finset.single_le_sum (f := fun t : K => detectionGain t + 32)
      (fun t _ => by linarith only [hgainDetect t])
      (Finset.mem_univ k)).trans (le_max_left _ _)
  have scalarAll (k) := preparedFiniteScheduleLocalScalarBounds_explicit
    m (degree k) (Cdetect k) (hdegree k)
    (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    nX (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
    Bstruct D pRadius Qstride Pscale coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    (sourceU k) (modelLog k) (sliceLog k) (Prho k)
    hB hD hpRadius.1 (hsourceU k) (hmodelLog k) hQstride (hlogs k).2.2.1
    (hsliceModel k) (hcountModel k) (hPkScale k) (hcoarse k) (hLate k)
  have scalar : PreparedUniformDegreeDirectScalarBounds m 0 nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
      (sampledSupportedSlicedDetectionConstant 0 Pdetect)
      Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel) Qstride (Pmaster kModel) Plate
      (detectionGain kModel) (Pphysical kModel) coarseTarget pRadius (u + 2 * p + 1)
      (modelLog kModel) (sliceLog kModel) := by
    have hstage : PreparedUniformDegreeDirectScalarBounds m (degree kModel) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
          (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
          (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        (Cdetect kModel) Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel)
        Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget pRadius
        (sourceU kModel) (modelLog kModel) (sliceLog kModel) := scalarAll kModel
    rw [hdegreeZero, hCzero, hModelSource] at hstage
    exact hstage
  have hGeometryZero : PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S 0
      (sampledSupportedSlicedDetectionConstant 0 Pdetect) nX
      Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel) Qstride
      (allocatedModelTestLog (u + 2 * p + 1) (modelLog kModel)) pRadius
      (2 * (u + 2 * p + 1) + 4 * modelLog kModel + 7) (detectionGain kModel) := by
    have hstage : PreparedUniformDegreeGeometryAt
        (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
        U b S (degree kModel) (Cdetect kModel) nX
        Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel) Qstride
        (pDetect kModel) pRadius (aDetect kModel) (detectionGain kModel) := hGeometryAll kModel
    have hpd : pDetect kModel = allocatedModelTestLog (u + 2 * p + 1) (modelLog kModel) := by
      change allocatedModelTestLog (sourceU kModel) (modelLog kModel) = _
      rw [hModelSource]
    have had : aDetect kModel = 2 * (u + 2 * p + 1) + 4 * modelLog kModel + 7 := by
      change 2 * sourceU kModel + 4 * modelLog kModel + 7 = _
      rw [hModelSource]
    rw [hdegreeZero, hCzero, hpd, had] at hstage
    exact hstage
  have hWitnessLate : allocatedWitnessScaleLog Pseed Qw ≤ Plate :=
    (preparedUniformDegreeDirectLate_extra (Pmaster kModel) Pscale
      (Pphysical kModel) coarseTarget (allocatedWitnessScaleLog Pseed Qw)).trans (hLate kModel)
  have hGainMaster : gainLog + (nX : ℝ) + 8 ≤ Pmaster kModel := by
    have hr := (hlogs kModel).2.2.1
    change gainLog + (nX : ℝ) + 8 ≤ Bstruct + D + pRadius + Qstride + Pphysical kModel +
      (sourceU kModel + modelLog kModel + pDetect kModel + Prho kModel + target kModel + detectionGain kModel + 32)
    linarith only [hgChart, hD, hpRadius.1, hQstride, hphysicalX kModel,
      hsourceU kModel, hmodelLog kModel, hpDetect kModel, hr, htarget kModel, hgainDetect kModel]
  refine ⟨(fun j => (hR j).1), σ, hσ, S, hpRadius.1,
    (fun j => (hR j).2), hσone, hσexp, hσinv, hFloor, hS, hgap, hGeometryAll, scalarAll, ?_, ?_, ?_, ?_⟩
  · intro k hconstant
    exact preparedFiniteScheduleGeometryDirectSource
      (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
      (U := U) (basis := b) (S := S) (hR := fun j => (hR j).1) (hσ := fun _ => hσ)
      (selection := enlargedPreparedCommonCanonicalSelection m
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
      (stride := stride) (N := N) (Pdetect := Pdetect) (sourceU := sourceU k)
      (pModel := modelLog k) (pSlice := sliceLog k) (Vtail := Vtail) (τ := τ)
      (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ)
      (Cdetect k) hconstant (hdegree k)
      Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
      (detectionGain k) (Pphysical k) coarseTarget pRadius (scalarAll k) (hGeometryAll k)
      (fun j => (hR j).2.1) (fun j => (hR j).2.2) (fun _ => hσone)
      (hS.trans (Real.exp_le_exp.mpr hWitnessLate))
      (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate prep
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k) ⟨j, Sum.inr i⟩)
      (fun j i => enlargedPreparedCommonSamplerBlock_uniform prep
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k) ⟨j, Sum.inr i⟩)
      (enlargedPreparedCommonKernel_analytic_capacity m
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
  · intro k hzero hconstant
    exact preparedFiniteScheduleGeometryModel
      (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
      (U := U) (basis := b) (S := S) (hR := fun j => (hR j).1) (hσ := fun _ => hσ)
      (selection := enlargedPreparedCommonCanonicalSelection m
        (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))
      (stride := stride) (N := N) (Pdetect := Pdetect) (sourceU := sourceU k)
      (pModel := modelLog k) (pSlice := sliceLog k) (Vtail := Vtail) (τ := τ)
      (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
      (degree k) (Cdetect k) hzero hconstant
      Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
      (detectionGain k) (Pphysical k) coarseTarget pRadius (scalarAll k) (hGeometryAll k)
      (fun j => (hR j).2.1) (fun j => (hR j).2.2) (fun _ => hσone)
      (hS.trans (Real.exp_le_exp.mpr hWitnessLate))
      (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate prep
        (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m) ⟨j, Sum.inr i⟩)
      (fun j i => enlargedPreparedCommonSamplerBlock_uniform prep
        (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m) ⟨j, Sum.inr i⟩)
      (enlargedPreparedCommonKernel_analytic_capacity m
        (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))
  · intro k hconstant
    exact preparedFiniteScheduleDegreeGeometryModel
      (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
      (U := U) (basis := b) (S := S) (hR := fun j => (hR j).1) (hσ := fun _ => hσ)
      (selection := enlargedPreparedCommonCanonicalSelection m
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
      (stride := stride) (N := N) (Pdetect := Pdetect) (sourceU := sourceU k)
      (pModel := modelLog k) (pSlice := sliceLog k) (Vtail := Vtail) (τ := τ)
      (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ)
      (Cdetect k) hconstant (hdegree k)
      Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
      (detectionGain k) (Pphysical k) coarseTarget pRadius (scalarAll k) (hGeometryAll k)
      (fun j => (hR j).2.1) (fun j => (hR j).2.2) (fun _ => hσone)
      (hS.trans (Real.exp_le_exp.mpr hWitnessLate))
      (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate prep
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k) ⟨j, Sum.inr i⟩)
      (fun j i => enlargedPreparedCommonSamplerBlock_uniform prep
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k) ⟨j, Sum.inr i⟩)
      (enlargedPreparedCommonKernel_analytic_capacity m
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
  · exact preparedUniformDegreeProductiveSource
      (prep := prep) (U := U) (b := b) (S := S) (hR := fun j => (hR j).1) (hσ := fun _ => hσ)
      (stride := stride) (N := N) (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
      Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel) Qstride (Pmaster kModel) Plate (detectionGain kModel)
      (Pphysical kModel) coarseTarget pRadius scalar hGeometryZero
      (fun j => (hR j).2.1) (fun j => (hR j).2.2)
      hu hp hSliceLog hCtail hForecastCap hForecastCapP
      Qgood hm hnX hCoord hpRadius.1 hPseed hQw hVlog hg hQgood hQexp
      hWitnessLate hgain hB hnChart hgChart hGainMaster rfl hS hgap

end Erdos3.VectorPolynomial

end

end OAI

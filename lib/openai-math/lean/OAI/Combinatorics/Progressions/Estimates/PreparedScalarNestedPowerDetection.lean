import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteNestedForwardCanonicalFixedCenterSource

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedEmptyLayerLocalLengthLog
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ : ℝ) (u model : K → ℝ) (k : K) : ℝ :=
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
  allocatedAffineLengthLog m D scale (rho k) (Pk k) (target k) (pDetect k + 2) (tmod k)

noncomputable def preparedEmptyLayerLocalScaleFloor
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ : ℝ) (u model : K → ℝ) : ℝ :=
  max (preparedEmptyLayerLocalTailWidthLog (G := G) m degree Cdetect nX count
    Bstruct pnum Qstride Qσ u model)
    (∑ k, max 0 (preparedEmptyLayerLocalLengthLog (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ u model k))

theorem PreparedEmptyLayerLocalScheduleBudget.lengthLog_mem
    {m : ℕ} {K G : Type} [Fintype K] [Fintype G]
    {degree Cdetect : K → ℕ} {nX count : ℕ}
    {Bstruct pnum Qstride Qσ requestedCoarse extraLate : ℝ}
    {u model : K → ℝ} {cap : ℝ}
    (h : PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ requestedCoarse extraLate u model cap) (k : K) :
    preparedEmptyLayerLocalLengthLog (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ u model k ∈ Set.Icc 0 cap :=
  (h.2.2.2.2.2 k).2.2.2.2.2.2.1

theorem PreparedEmptyLayerLocalScheduleBudget.scaleFloor_le
    {m nStages : ℕ} {K G : Type} [Fintype K] [Fintype G]
    {degree Cdetect : K → ℕ} {nX count : ℕ}
    {Bstruct pnum Qstride Qσ requestedCoarse extraLate : ℝ}
    {u model : K → ℝ} {cap : ℝ}
    (h : PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ requestedCoarse extraLate u model cap)
    (hCard : Fintype.card K ≤ nStages) (hcap : 0 ≤ cap) :
    preparedEmptyLayerLocalScaleFloor (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ u model ≤
      (probabilityProfileLipschitz : ℝ) + 12 + ((nStages : ℝ) + 3) * cap := by
  have hsum : (∑ k, max 0 (preparedEmptyLayerLocalLengthLog (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ u model k)) ≤ (nStages : ℝ) * cap := by
    calc
      _ ≤ ∑ _k : K, cap := Finset.sum_le_sum (fun k _ => max_le hcap (h.lengthLog_mem k).2)
      _ = (Fintype.card K : ℝ) * cap := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hCard) hcap
  unfold preparedEmptyLayerLocalScaleFloor
  apply max_le
  · have hwidth := h.tailWidthLog_le
    have hprod : 0 ≤ (nStages : ℝ) * cap := mul_nonneg (Nat.cast_nonneg _) hcap
    nlinarith only [hwidth, hprod]
  · have hprofile := NNReal.coe_nonneg probabilityProfileLipschitz
    nlinarith only [hsum, hprofile, hcap]

theorem exists_preparedScalarFiniteSchedule_early_scale_power_budget
    (s nStages inputPower : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ {nX : ℕ} {K : Type} [Fintype K]
        (degree : K → ℕ) (Bstruct : ℝ) (sourceU modelLog : K → ℝ),
        Fintype.card K ≤ nStages → (∀ k, degree k ≤ s) → (nX : ℝ) ≤ p →
        Bstruct ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        (∀ k, sourceU k ∈ Set.Icc 0 ((p + 2) ^ inputPower)) →
        (∀ k, modelLog k ∈ Set.Icc 0 ((p + 2) ^ inputPower)) →
        let Cdetect := fun k => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
        PreparedEmptyLayerLocalScheduleBudget (G := Fin (scalarNativeDimension s))
          (max s 1) degree Cdetect nX (scalarNativeDimension s)
          Bstruct (scalarNativeDimension s : ℝ) 0 0 0 0 sourceU modelLog ((p + 2) ^ C) ∧
        preparedEmptyLayerLocalScaleFloor (G := Fin (scalarNativeDimension s))
          (max s 1) degree Cdetect nX (scalarNativeDimension s)
          Bstruct (scalarNativeDimension s : ℝ) 0 0 sourceU modelLog ≤ (p + 2) ^ C := by
  obtain ⟨A, _, hCore⟩ := exists_preparedScalarFiniteSchedule_power_budget s nStages inputPower Pdetect
  let poly : Polynomial ℕ := Polynomial.C (⌈(probabilityProfileLipschitz : ℝ)⌉₊ + 12) +
    Polynomial.C (nStages + 4) * (Polynomial.X + 2) ^ A
  obtain ⟨C, hC, hPoly⟩ := exists_natPolynomial_fixed_power_budget poly
  refine ⟨C, hC, ?_⟩
  intro p hp nX K _ degree Bstruct sourceU modelLog hCard hdegree hnX hB hu hmodel Cdetect
  obtain ⟨hSchedule, _⟩ := hCore hp degree Bstruct 0 sourceU modelLog
    hCard hdegree hnX hB ⟨le_rfl, by positivity⟩ hu hmodel
  have hcap : 0 ≤ (p + 2) ^ A := by positivity
  have hmajor : (⌈(probabilityProfileLipschitz : ℝ)⌉₊ : ℝ) + 12 +
      ((nStages : ℝ) + 4) * (p + 2) ^ A ≤ (p + 2) ^ C := by
    simpa [poly, Polynomial.eval₂_pow] using hPoly p hp
  have hceil0 : (0 : ℝ) ≤ ⌈(probabilityProfileLipschitz : ℝ)⌉₊ := Nat.cast_nonneg _
  have hprod : 0 ≤ (nStages : ℝ) * (p + 2) ^ A := mul_nonneg (Nat.cast_nonneg _) hcap
  have hcapUp : (p + 2) ^ A ≤ (p + 2) ^ C := by nlinarith only [hmajor, hceil0, hprod, hcap]
  refine ⟨hSchedule.mono hcapUp, ?_⟩
  have hfloor := hSchedule.scaleFloor_le hCard hcap
  have hprofile := Nat.le_ceil (probabilityProfileLipschitz : ℝ)
  exact hfloor.trans (by nlinarith only [hmajor, hprofile, hcap])

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedFiniteNestedForwardFixedCenterThreshold
    {outerDepth innerDepth cutoff : ℕ} (A : ℕ) (constants : ℕ → ℕ)
    (x gainLog stageLog : ℝ)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : ℝ :=
  let seed := preparedFiniteNestedForwardAllDegreeSeed A constants x k
  Real.exp (-(2 * preparedFiniteForwardModelPrecision A constants k.2.1.val seed gainLog stageLog +
    4 * preparedFiniteForwardWork A constants k.2.1.val seed + 8))

theorem preparedFiniteNestedForwardFixedCenterThreshold_bounds
    {outerDepth innerDepth cutoff : ℕ} (A Cdirect : ℕ) (constants : ℕ → ℕ)
    {x gainLog stageLog : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    let seed := preparedFiniteNestedForwardAllDegreeSeed A constants x k
    let sourceU := preparedFiniteForwardPairedSourcePrecision A Cdirect constants k.2.1.val
      k.2.2.2 seed gainLog stageLog
    let work := preparedFiniteForwardWork A constants k.2.1.val seed
    let α := preparedFiniteNestedForwardFixedCenterThreshold A constants x gainLog stageLog k
    0 < α ∧ Real.exp (-(2 * sourceU + 4 * work + 7)) ≤ α / 2 ∧
      α / 2 ≤ 1 ∧ α ≤ Real.exp (-gainLog) / 2 := by
  intro seed sourceU work α
  have hseed : x ≤ seed := le_preparedFiniteNestedForwardAllDegreeSeed A constants hA hx k
  have hseed0 : 0 ≤ seed := hx.trans hseed
  have hg' : gainLog ∈ Set.Icc 0 seed := ⟨hg.1, hg.2.trans hseed⟩
  have hs' : stageLog ∈ Set.Icc 0 seed := ⟨hs.1, hs.2.trans hseed⟩
  exact ⟨Real.exp_pos _,
    preparedFiniteForwardFixedCenterThreshold_lower A Cdirect constants k.2.1.val k.2.2.2
      hseed0 hg' hs',
    preparedFiniteForwardFixedCenterThreshold_half_le_one A constants k.2.1.val hseed0 hg' hs',
    preparedFiniteForwardInnerDetectionThreshold_bound A constants k.2.1.val hseed0 hg' hs'⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteNestedForwardScalarBounds
    {outerDepth innerDepth cutoff : ℕ} (A Cdirect Cslice : ℕ)
    (constants : ℕ → ℕ) (count : ℕ) {x gainLog stageLog : ℝ}
    (hA : 2 ≤ A) (hSlice : Cslice + 1 ≤ A)
    (hx : 0 ≤ x) (hcount : (count : ℝ) ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    ∀ k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff,
    let seed := preparedFiniteNestedForwardAllDegreeSeed A constants x k
    let sourceU := preparedFiniteForwardPairedSourcePrecision A Cdirect constants k.2.1.val
      k.2.2.2 seed gainLog stageLog
    let work := preparedFiniteForwardWork A constants k.2.1.val seed
    let sliceLog := (preparedFiniteForwardParameter A constants k.2.1.val seed + Cslice) ^ Cslice
    let α := preparedFiniteNestedForwardFixedCenterThreshold A constants x gainLog stageLog k
    0 ≤ sourceU ∧ 0 ≤ work ∧ sliceLog ≤ work ∧ (count : ℝ) ≤ Real.exp work ∧
      Real.exp (-(2 * sourceU + 4 * work + 7)) ≤ α / 2 ∧ α / 2 ≤ 1 ∧
      (count : ℝ) ≤ (preparedFiniteForwardDetectorPolynomial cutoff).eval₂
        (Nat.castRingHom ℝ) (allocatedModelTestLog sourceU work) := by
  intro k seed sourceU work sliceLog α
  have hseed : x ≤ seed := le_preparedFiniteNestedForwardAllDegreeSeed A constants hA hx k
  have hseed0 : 0 ≤ seed := hx.trans hseed
  have hg' : gainLog ∈ Set.Icc 0 seed := ⟨hg.1, hg.2.trans hseed⟩
  have hs' : stageLog ∈ Set.Icc 0 seed := ⟨hs.1, hs.2.trans hseed⟩
  have hcountSeed : (count : ℝ) ≤ seed := hcount.trans hseed
  have hu : 0 ≤ sourceU := preparedFiniteForwardPairedSourcePrecision_nonneg
    A Cdirect constants k.2.1.val k.2.2.2 hseed0 hg' hs'
  have hscalar := preparedFiniteForward_model_scalar_bounds A constants k.2.1.val count
    hA hseed0 hcountSeed
  have hslice := preparedFiniteForward_controlled_slice_bounds A Cslice constants k.2.1.val
    count hA hSlice hseed0 hcountSeed
  have hthreshold := preparedFiniteNestedForwardFixedCenterThreshold_bounds
    A Cdirect constants hA hx hg hs k
  have hcountWork : (count : ℝ) ≤ work :=
    hcountSeed.trans ((le_preparedFiniteForwardParameter A constants k.2.1.val hseed0).trans
      hscalar.2.1)
  exact ⟨hu, hscalar.1, hslice.2.1, hscalar.2.2.1,
    hthreshold.2.1, hthreshold.2.2.1,
    hcountWork.trans (preparedFiniteForwardDetectorPolynomial_bounds cutoff hu hscalar.1).1⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
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

theorem preparedRelativePositiveTerminalDetection
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
        (preparedFiniteNestedForwardFixedCenterThreshold Aexp constants Bstruct gainLog stageLog k)) :
    let seed := candidateNestedForwardSeed Aexp constants (s + 1) (2 * s + 2) Bstruct
    let u := preparedFiniteForwardModelPrecision Aexp constants (s + 1) seed gainLog stageLog
    let p := preparedFiniteForwardWork Aexp constants (s + 1) seed
    let sliceLog := (preparedFiniteForwardParameter Aexp constants (s + 1) seed + Cslice) ^ Cslice
    let testLog := (preparedFiniteForwardDetectorPolynomial s).eval₂ (Nat.castRingHom ℝ)
      (allocatedModelTestLog
        (preparedFiniteForwardSourcePrecision Aexp constants (s + 1) seed gainLog stageLog) p)
    let native := (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m 0) 1
      (Pmaster (preparedFiniteNestedForwardAllDegreeAnchor (2 * s + 2) (s + 1) s)) Plate).nativeBudget
    A.NativeDetection 0 sliceLog testLog native (Real.exp (-(2 * u + 4 * p + 8))) := by
  simpa only [preparedFiniteNestedForwardFixedCenterThreshold,
    preparedFiniteNestedForwardAllDegreeAnchor, preparedFiniteNestedForwardAllDegreeDegree,
    preparedFiniteNestedForwardAllDegreeStage, preparedFiniteNestedForwardAllDegreeIsDirect,
    preparedFiniteNestedForwardAllDegreeSeed, preparedFiniteForwardPairedSourcePrecision_model,
    Fin.val_zero, Nat.zero_add]
    using hdirect (preparedFiniteNestedForwardAllDegreeAnchor (2 * s + 2) (s + 1) s)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

theorem exists_preparedScalarNestedInput_power_budget
    (outerDepth innerDepth cutoff exponent Cdirect basePower : ℕ)
    (constants : ℕ → ℕ) (hA : 2 ≤ exponent) :
    ∃ inputPower : ℕ, 2 ≤ inputPower ∧ ∀ {p : ℝ}, 0 ≤ p →
      let B := (p + 2) ^ basePower
      B ∈ Set.Icc 0 ((p + 2) ^ inputPower) ∧
      ∀ k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff,
        preparedFiniteForwardPairedSourcePrecision exponent Cdirect constants
          (preparedFiniteNestedForwardAllDegreeStage k).val
          (preparedFiniteNestedForwardAllDegreeIsDirect k)
          (preparedFiniteNestedForwardAllDegreeSeed exponent constants B k) B B ∈
            Set.Icc 0 ((p + 2) ^ inputPower) ∧
        preparedFiniteForwardWork exponent constants
          (preparedFiniteNestedForwardAllDegreeStage k).val
          (preparedFiniteNestedForwardAllDegreeSeed exponent constants B k) ∈
            Set.Icc 0 ((p + 2) ^ inputPower) := by
  obtain ⟨D, _, hlocal⟩ := exists_candidateNestedForwardLocal_budget
    exponent Cdirect constants innerDepth outerDepth hA
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ basePower +
    ((Polynomial.X + 2) ^ basePower + 2) ^ D
  obtain ⟨inputPower, hInput, hQ⟩ := exists_natPolynomial_fixed_power_budget Q
  refine ⟨inputPower, hInput, ?_⟩
  intro p hp B
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmajor : B + (B + 2) ^ D ≤ (p + 2) ^ inputPower := by
    simpa [Q, B, Polynomial.eval₂_pow] using hQ p hp
  have hnonneg : 0 ≤ (B + 2) ^ D := by positivity
  have hcap : (B + 2) ^ D ≤ (p + 2) ^ inputPower := by
    linarith only [hmajor, hB]
  refine ⟨⟨hB, by linarith only [hmajor, hnonneg]⟩, ?_⟩
  intro k
  have h := hlocal (gainLog := B) (stageLog := B) hB ⟨hB, le_rfl⟩ ⟨hB, le_rfl⟩
    k.1.val (Nat.le_of_lt_succ k.1.isLt) k.2.1.val (Nat.le_of_lt_succ k.2.1.isLt)
  have hu := h.2.2.2.2.2 k.2.2.2
  have hw := h.2.2.1
  exact ⟨⟨hu.1, hu.2.trans hcap⟩, ⟨hw.1, hw.2.trans hcap⟩⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

namespace AllocatedExternalCandidateSampler
variable {s nX : ℕ}
    {I₀ J₀ : Fin 0 → Type} [∀ j, Fintype (I₀ j)] [∀ j, Fintype (J₀ j)]
    {n₀ : Fin 0 → ℕ} {B₀ : LayerSamplerAxis I₀ n₀ → Type} [∀ a, Fintype (B₀ a)]
    {U₀ : ∀ j, Submodule ℝ (J₀ j → ℝ)}
    {b₀ : ∀ j, Basis (Fin (n₀ j)) ℝ (euclideanSubspace (U₀ j))ᗮ}
    {R₀ σ₀ : Fin 0 → ℝ}
    {S₀ : LayerSamplerScale (G := Fin (scalarNativeDimension s)) B₀ U₀ b₀ R₀ σ₀}
    {hb₀ : ∀ j, span ℤ (Set.range (b₀ j)) = projectedIntegerLattice (euclideanSubspace (U₀ j))}
    {o₀ : ∀ j, OrthonormalBasis (I₀ j) ℝ (euclideanSubspace (U₀ j))}
    {hR₀ : ∀ j, 0 < R₀ j} {hσ₀ : ∀ j, 0 < σ₀ j}
    {N : Fin nX → ℕ} {poly₀ : ∀ j, VectorPolynomial (Fin nX) ℝ (J₀ j → ℝ)}
    {hmem₀ : ∀ j e, coefficients (poly₀ j) e ∈ U₀ j}
    {τ ξ₀ : ℝ}
    {center₀ : CoefficientTorus (K := LayerSamplerVariables (Fin (scalarNativeDimension s)) I₀ n₀ B₀) U₀}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J₀ j)) (euclideanSubspace (U₀ j)))]

theorem nativeDetection_of_preparedScalarNestedSchedule
    (A₀ : AllocatedExternalCandidateSampler B₀ U₀ b₀ S₀ hb₀ o₀ hR₀ hσ₀
      N poly₀ hmem₀ τ ξ₀ (fun _ : Fin nX => 1) {0} center₀)
    (outerDepth innerDepth exponent Cslice Cdirect : ℕ) (constants : ℕ → ℕ)
    (Bstruct gainLog stageLog extraLate p : ℝ)
    (hA : 3 ≤ exponent) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hnum : (scalarNativeDimension s : ℝ) ≤ Bstruct)
    (hg : gainLog ∈ Set.Icc 0 Bstruct) (hs : stageLog ∈ Set.Icc 0 Bstruct)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (hp : 2 ≤ p) (hX : (nX : ℝ) ≤ p) (hpB : p ≤ Bstruct)
    (htrim : τ = unconditionedSpatialTrimFraction nX (Real.exp (-p))) :
    let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth s
    let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
    let stage : K → ℕ := fun k => (preparedFiniteNestedForwardAllDegreeStage k).val
    let direct : K → Bool := preparedFiniteNestedForwardAllDegreeIsDirect
    let seed : K → ℝ := preparedFiniteNestedForwardAllDegreeSeed exponent constants Bstruct
    let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision exponent Cdirect
      constants (stage k) (direct k) (seed k) gainLog stageLog
    let modelLog := fun k : K => preparedFiniteForwardWork exponent constants (stage k) (seed k)
    let sliceLog := fun k : K =>
      (preparedFiniteForwardParameter exponent constants (stage k) (seed k) + Cslice) ^ Cslice
    let α := preparedFiniteNestedForwardFixedCenterThreshold exponent constants Bstruct gainLog stageLog
    let Pdetect := preparedFiniteForwardDetectorPolynomial s
    let q := max s 1
    let count := scalarNativeDimension s
    let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let pRadius := allocatedCommonProductRadiusLog q Bstruct Bstruct
    let D := allocatedComparisonDimension q (count : ℝ)
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun k => slicedDetectionGainLog (degree k) (Cdetect k)
      count (pDetect k) (pDetect k) (aDetect k)
    let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1))
      (Fin (scalarNativeDimension s)) (detectionGain k + pDetect k + 4)
    let Pphysical := fun k => preparedFiniteScheduleLocalPhysical q nX count 0 (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun k => target k + D * ((q * 2 ^ (q + 1) : ℕ) * Pk k) + 5
    let Prho := fun k => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
    let Ptail := fun k => affineProfileToleranceEnvelope q D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail 0
    let Tmod := fun k => ((q + 1 : ℕ) : ℝ) * Pk k + nX * 0
    let lengthLogs := fun k => allocatedAffineLengthLog q D Pscale (Prho k) (Pk k)
      (target k) (pDetect k + 2) (Tmod k)
    let Pmaster := fun k => preparedFiniteScheduleLocalMaster Bstruct D pRadius 0
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain 0
    let localLate := fun k => preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget extraLate
    let Plate := ∑ k, localLate k
    let detectorRequired := fun k : K =>
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q (degree k))
        (degree k + 1) (Pmaster k) Plate).required
    let scaleFloor := max (((probabilityProfileLipschitz : ℝ) + 8) + (D + 4) + pRadius + Pscale)
      (∑ k : K, max 0 (lengthLogs k))
    let spatialFloor := preparedFiniteNestedSourceRequired exponent constants innerDepth outerDepth s
      Bstruct 0 0 detectorRequired
    Real.exp scaleFloor ≤ S₀.value →
    (S₀.value : ℝ) ≤ Real.exp extraLate →
    (∀ i, Real.exp spatialFloor ≤ (N i : ℝ)) →
    ∀ k : K, A₀.NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedFiniteNestedSourceNative q (Fin (scalarNativeDimension s)) count nX Pdetect
        exponent Cdirect constants Bstruct count 0 gainLog stageLog Plate k) (α k) := by
  intro K degree stage direct seed sourceU modelLog sliceLog α Pdetect q count Cdetect
    pRadius D pDetect aDetect detectionGain Pk Pphysical target E Prho Ptail Pscale Tmod
    lengthLogs Pmaster coarseTarget localLate Plate detectorRequired scaleFloor spatialFloor
    hscale hSupper hsize
  have hB : 0 ≤ Bstruct := by linarith
  have hA2 : 2 ≤ exponent := by omega
  have hscalar := preparedFiniteNestedForwardScalarBounds
    (outerDepth := outerDepth) (innerDepth := innerDepth) (cutoff := s) exponent Cdirect Cslice constants
    count hA2 hSliceExponent hB hnum hg hs
  have hu (k : K) : 0 ≤ sourceU k := (hscalar k).1
  have hw (k : K) : 0 ≤ modelLog k := (hscalar k).2.1
  have hslice (k : K) : sliceLog k ≤ modelLog k := (hscalar k).2.2.1
  have hcount (k : K) : (count : ℝ) ≤ Real.exp (modelLog k) := (hscalar k).2.2.2.1
  have hαLower (k : K) : Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2 :=
    (hscalar k).2.2.2.2.1
  have hαHalf (k : K) : α k / 2 ≤ 1 := (hscalar k).2.2.2.2.2.1
  have hdimension (k : K) : (count : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)) :=
    (hscalar k).2.2.2.2.2.2
  have hlength (k : K) : Real.exp (lengthLogs k) ≤ S₀.value := by
    apply le_trans (Real.exp_le_exp.mpr (?_)) hscale
    exact (le_max_right 0 (lengthLogs k)).trans
      ((Finset.single_le_sum (fun _ _ => le_max_left (0 : ℝ) _) (Finset.mem_univ k)).trans
        (le_max_right _ _))
  have hwidth : Real.exp (((probabilityProfileLipschitz : ℝ) + 8) + (D + 4) + pRadius + Pscale) ≤
      S₀.value := (Real.exp_le_exp.mpr (le_max_left _ _)).trans hscale
  have hsizeEach (k : K) (i) : Real.exp (detectorRequired k) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (detectorRequired_le_preparedFiniteNestedSourceRequired exponent
      constants innerDepth outerDepth s Bstruct 0 0 detectorRequired k)).trans (hsize i)
  have htrimBounds (k : K) : τ⁻¹ ≤ Real.exp (Pphysical k) ∧
      τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 := by
    rw [htrim]
    exact preparedScalarFiniteScheduleLocalPhysical_nested_exp_trim q nX count (degree k)
      (Cdetect k) exponent (stage k) innerDepth k.1.val (Fin (scalarNativeDimension s))
      constants hp hX hA hpB (hu k)
  let anchor : K := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth s
  have hdetect : ∀ k : K, A₀.NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k) :=
    A₀.nativeDetection_of_preparedScalarFiniteSchedule degree
      (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_refl s))
      Pdetect Bstruct extraLate sourceU modelLog sliceLog α hB hnum hu hw hslice hcount
      hαLower hαHalf hprofile hcutoff hdimension hlength hwidth hSupper hsizeEach
      (fun k => (htrimBounds k).1) (htrimBounds anchor).2.1 (htrimBounds anchor).2.2
  intro k
  exact @hdetect k

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def PreparedScalarNestedPowerDetection
    (s outerDepth innerDepth exponent Cslice Cdirect : ℕ) (constants : ℕ → ℕ)
    (basePower earlyExponent latePower sizeExponent : ℕ) : Prop :=
  ∀ {nX : ℕ} {p : ℝ}, 2 ≤ p → (nX : ℝ) ≤ p →
    ∀ {I₀ J₀ : Fin 0 → Type} [∀ j, Fintype (I₀ j)] [∀ j, Fintype (J₀ j)]
      {n₀ : Fin 0 → ℕ} {B₀ : LayerSamplerAxis I₀ n₀ → Type} [∀ a, Fintype (B₀ a)]
      {U₀ : ∀ j, Submodule ℝ (J₀ j → ℝ)}
      {b₀ : ∀ j, Basis (Fin (n₀ j)) ℝ (euclideanSubspace (U₀ j))ᗮ}
      {R₀ σ₀ : Fin 0 → ℝ}
      {S₀ : LayerSamplerScale (G := Fin (scalarNativeDimension s)) B₀ U₀ b₀ R₀ σ₀}
      {hb₀ : ∀ j, span ℤ (Set.range (b₀ j)) = projectedIntegerLattice (euclideanSubspace (U₀ j))}
      {o₀ : ∀ j, OrthonormalBasis (I₀ j) ℝ (euclideanSubspace (U₀ j))}
      {hR₀ : ∀ j, 0 < R₀ j} {hσ₀ : ∀ j, 0 < σ₀ j}
      {N : Fin nX → ℕ} {poly₀ : ∀ j, VectorPolynomial (Fin nX) ℝ (J₀ j → ℝ)}
      {hmem₀ : ∀ j e, coefficients (poly₀ j) e ∈ U₀ j}
      {τ ξ₀ : ℝ}
      {center₀ : CoefficientTorus
        (K := LayerSamplerVariables (Fin (scalarNativeDimension s)) I₀ n₀ B₀) U₀}
      [∀ j, IsZLattice ℝ
        (latticeSection (standardEuclideanLattice (J₀ j)) (euclideanSubspace (U₀ j)))]
      (A₀ : AllocatedExternalCandidateSampler B₀ U₀ b₀ S₀ hb₀ o₀ hR₀ hσ₀
        N poly₀ hmem₀ τ ξ₀ (fun _ : Fin nX => 1) {0} center₀),
      τ = unconditionedSpatialTrimFraction nX (Real.exp (-p)) →
      Real.exp ((p + 2) ^ earlyExponent) ≤ S₀.value →
      (S₀.value : ℝ) ≤ Real.exp ((p + 2) ^ latePower) →
      (∀ i, Real.exp ((p + 2) ^ sizeExponent) ≤ (N i : ℝ)) →
      let Bstruct := (p + 2) ^ basePower
      let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth s
      let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
      let stage : K → ℕ := fun k => (preparedFiniteNestedForwardAllDegreeStage k).val
      let seed : K → ℝ := preparedFiniteNestedForwardAllDegreeSeed exponent constants Bstruct
      let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision exponent Cdirect
        constants (stage k) (preparedFiniteNestedForwardAllDegreeIsDirect k) (seed k) Bstruct Bstruct
      let modelLog := fun k : K => preparedFiniteForwardWork exponent constants (stage k) (seed k)
      let sliceLog := fun k : K =>
        (preparedFiniteForwardParameter exponent constants (stage k) (seed k) + Cslice) ^ Cslice
      let α := preparedFiniteNestedForwardFixedCenterThreshold exponent constants Bstruct Bstruct Bstruct
      let Pdetect := preparedFiniteForwardDetectorPolynomial s
      ∃ Plate : ℝ, 0 ≤ Plate ∧
        (∀ k : K, A₀.NativeDetection (degree k) (sliceLog k)
          (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
          (preparedFiniteNestedSourceNative (max s 1) (Fin (scalarNativeDimension s))
            (scalarNativeDimension s) nX Pdetect exponent Cdirect constants
            Bstruct (scalarNativeDimension s) 0 Bstruct Bstruct Plate k) (α k)) ∧
        ∀ (outer : Fin (outerDepth + 1)) (degree : Fin (s + 1)) (i : Fin nX),
          Real.exp (preparedFiniteForwardCumulative exponent constants degree.val
            (candidateNestedForwardSeed exponent constants innerDepth outer.val Bstruct)) ≤ (N i : ℝ)

theorem exists_preparedScalarNestedSchedule_power_detection
    (s outerDepth innerDepth exponent Cslice Cdirect : ℕ) (constants : ℕ → ℕ)
    (hA : 3 ≤ exponent) (hSlice : Cslice + 1 ≤ exponent) (hcutoff : s ≤ innerDepth) :
    ∃ baseMin : ℕ, 1 ≤ baseMin ∧ ∀ basePower : ℕ, baseMin ≤ basePower →
      ∃ earlyExponent : ℕ, 2 ≤ earlyExponent ∧ ∀ latePower : ℕ,
        ∃ sizeExponent : ℕ, 2 ≤ sizeExponent ∧
          PreparedScalarNestedPowerDetection s outerDepth innerDepth exponent Cslice Cdirect
            constants basePower earlyExponent latePower sizeExponent := by
  obtain ⟨baseMin, hBaseMin, hstruct⟩ := exists_preparedScalarStructuralBasePower s
  refine ⟨baseMin, hBaseMin, ?_⟩
  intro basePower hBasePower
  have hBase : 1 ≤ basePower := hBaseMin.trans hBasePower
  have hA2 : 2 ≤ exponent := by omega
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth s
  let nStages := Fintype.card K
  let Pdetect := preparedFiniteForwardDetectorPolynomial s
  obtain ⟨inputPower, _, hinput⟩ := exists_preparedScalarNestedInput_power_budget
    outerDepth innerDepth s exponent Cdirect basePower constants hA2
  obtain ⟨earlyExponent, hEarly, hearly⟩ :=
    exists_preparedScalarFiniteSchedule_early_scale_power_budget s nStages inputPower Pdetect
  refine ⟨earlyExponent, hEarly, ?_⟩
  intro latePower
  obtain ⟨lateExponent, _, hlate⟩ :=
    exists_preparedScalarFiniteSchedule_power_budget s nStages (max inputPower latePower) Pdetect
  obtain ⟨sizeExponent, hSize, hrequired⟩ :=
    exists_preparedFiniteNestedSourceRequired_raised_power_budget exponent constants
      innerDepth outerDepth basePower lateExponent nStages hA2 hBase
  refine ⟨sizeExponent, hSize, ?_⟩
  intro nX p hp hX I₀ J₀ _ _ n₀ B₀ _ U₀ b₀ R₀ σ₀ S₀ hb₀ o₀ hR₀ hσ₀
    N poly₀ hmem₀ τ ξ₀ center₀ _ A₀ htrim hscale hSupper hsize
  let Bstruct : ℝ := (p + 2) ^ basePower
  let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
  let stage : K → ℕ := fun k => (preparedFiniteNestedForwardAllDegreeStage k).val
  let seed : K → ℝ := preparedFiniteNestedForwardAllDegreeSeed exponent constants Bstruct
  let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision exponent Cdirect
    constants (stage k) (preparedFiniteNestedForwardAllDegreeIsDirect k) (seed k) Bstruct Bstruct
  let modelLog := fun k : K => preparedFiniteForwardWork exponent constants (stage k) (seed k)
  let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ Bstruct := by dsimp [Bstruct]; positivity
  have hstructData := hstruct basePower hBasePower p hp
  have hinputData := hinput hp0
  have hcard : Fintype.card K ≤ nStages := le_rfl
  have hdegree (k : K) : degree k ≤ s :=
    preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_refl s) k
  have hu (k : K) : sourceU k ∈ Set.Icc 0 ((p + 2) ^ inputPower) := (hinputData.2 k).1
  have hm (k : K) : modelLog k ∈ Set.Icc 0 ((p + 2) ^ inputPower) := (hinputData.2 k).2
  have hEarlyData := hearly hp0 degree Bstruct sourceU modelLog hcard hdegree hX hinputData.1 hu hm
  have hbase : 1 ≤ p + 2 := by linarith
  have hInputLift : (p + 2) ^ inputPower ≤ (p + 2) ^ max inputPower latePower :=
    pow_le_pow_right₀ hbase (le_max_left inputPower latePower)
  have hLateLift : (p + 2) ^ latePower ≤ (p + 2) ^ max inputPower latePower :=
    pow_le_pow_right₀ hbase (le_max_right inputPower latePower)
  have lift {x : ℝ} (hx : x ∈ Set.Icc 0 ((p + 2) ^ inputPower)) :
      x ∈ Set.Icc 0 ((p + 2) ^ max inputPower latePower) := ⟨hx.1, hx.2.trans hInputLift⟩
  have hLateData := (hlate hp0 degree Bstruct ((p + 2) ^ latePower) sourceU modelLog
    hcard hdegree hX (lift hinputData.1) ⟨by positivity, hLateLift⟩
    (fun k => lift (hu k)) (fun k => lift (hm k))).1
  have hActual := A₀.nativeDetection_of_preparedScalarNestedSchedule
    outerDepth innerDepth exponent Cslice Cdirect constants Bstruct Bstruct Bstruct
    ((p + 2) ^ latePower) p hA hSlice hstructData.1 ⟨hB, le_rfl⟩ ⟨hB, le_rfl⟩
    hstructData.2.1 hstructData.2.2.1 hp hX hstructData.2.2.2 htrim
  refine ⟨_, hLateData.2.2.2.2.1.1, ?_, ?_⟩
  · apply hActual
    · exact (Real.exp_le_exp.mpr hEarlyData.2).trans hscale
    · exact hSupper
    · intro i
      apply (Real.exp_le_exp.mpr (hrequired hp K s hcutoff hcard _ ?_)).trans (hsize i)
      intro k
      exact (hLateData.2.2.2.2.2 k).2.2.2.2.2.2.2.2.required.2
  · intro outer degree i
    exact (Real.exp_le_exp.mpr ((cumulative_le_preparedFiniteNestedSourceRequired
      exponent constants innerDepth outerDepth s Bstruct 0 0 (fun _ : K => 0) outer degree).trans
      (hrequired hp K s hcutoff hcard (fun _ : K => 0) (fun _ => by positivity)))).trans (hsize i)

end Erdos3.VectorPolynomial

end

end OAI

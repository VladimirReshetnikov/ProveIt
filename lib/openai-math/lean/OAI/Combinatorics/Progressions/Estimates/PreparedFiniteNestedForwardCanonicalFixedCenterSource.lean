import OAI.Combinatorics.Progressions.Dynamics.UnconditionedWidthExponentialBudget
import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteNestedAnchorRequiredPower
import OAI.Combinatorics.Progressions.Estimates.PreparedReadyPaddedRelativeInitialization
import OAI.Combinatorics.Progressions.Estimates.PreparedScalarFiniteScheduleCandidateDetection
import OAI.Combinatorics.Progressions.Geometry.PreparedGeometryDecidableTransport

namespace OAI

section

namespace Erdos3

theorem unconditionedSpatialTrimFraction_inv_pow_bound {p : ℝ} {d : ℕ}
    (hp : 2 ≤ p) (hd : (d : ℝ) ≤ p) :
    (unconditionedSpatialTrimFraction d (Real.exp (-p)))⁻¹ ≤
      Real.exp ((p + 2) ^ 3) := by
  apply (unconditionedSpatialTrimFraction_inv_exp_bound hd).trans
  apply Real.exp_le_exp.mpr
  have hs : 16 ≤ (p + 2) ^ 2 := by nlinarith
  have hm := mul_nonneg (sub_nonneg.mpr hs) (by linarith : 0 ≤ p + 2)
  nlinarith

theorem unconditionedSpatialTrimFraction_exp_bounds {p : ℝ} {d : ℕ}
    (hp : 2 ≤ p) (hd : (d : ℝ) ≤ p) :
    let τ := unconditionedSpatialTrimFraction d (Real.exp (-p))
    0 < τ ∧ τ ≤ 1 / 2 ∧ (d : ℝ) * τ ≤ 1 / 2 ∧
      τ⁻¹ ≤ Real.exp ((p + 2) ^ 3) := by
  have hsurplus : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨hτ, hhalf, hdim⟩ :=
    unconditionedSpatialTrimFraction_bounds d (Real.exp_pos _) hsurplus
  refine ⟨hτ, hhalf, ?_, unconditionedSpatialTrimFraction_inv_pow_bound hp hd⟩
  linarith

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators

theorem preparedUniformDegreeDirectLate_extra_le
    (Pmaster Pscale Pphysical coarseTarget extraLate : ℝ) :
    extraLate ≤ preparedUniformDegreeDirectLate Pmaster Pscale Pphysical coarseTarget extraLate :=
  (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))

theorem preparedFiniteScheduleDirectLate_extra_le_sum
    {Stage : Type*} [Fintype Stage] (k₀ : Stage)
    (Pmaster Pphysical : Stage → ℝ) (Pscale coarseTarget extraLate : ℝ)
    (hmaster : ∀ k, 0 ≤ Pmaster k) :
    extraLate ≤ ∑ k, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget extraLate := by
  apply (preparedUniformDegreeDirectLate_extra_le (Pmaster k₀) Pscale
    (Pphysical k₀) coarseTarget extraLate).trans
  exact Finset.single_le_sum
    (f := fun k => preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget extraLate)
    (fun k _ => (hmaster k).trans (le_max_left _ _)) (Finset.mem_univ k₀)

theorem preparedFiniteScheduleScale_le_exp_late
    {Stage : Type*} [Fintype Stage] (k₀ : Stage)
    (Pmaster Pphysical : Stage → ℝ) (Pscale coarseTarget extraLate scale : ℝ)
    (hmaster : ∀ k, 0 ≤ Pmaster k) (hscale : scale ≤ Real.exp extraLate) :
    scale ≤ Real.exp (∑ k, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget extraLate) :=
  hscale.trans (Real.exp_le_exp.mpr (preparedFiniteScheduleDirectLate_extra_le_sum
    k₀ Pmaster Pphysical Pscale coarseTarget extraLate hmaster))

theorem preparedFiniteSchedule_kernel_input_le
    (I G : Type*) [Fintype I] [Fintype G] {R : ℝ} (hR : 0 ≤ R) :
    R ≤ scalarKernelLogarithmicBudget I G R := by
  let base : ℝ := 10 + (Fintype.card I : ℝ) + Fintype.card G +
    Fintype.card G * (Fintype.card I + 1) + R
  have hI : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have hG : (0 : ℝ) ≤ Fintype.card G := Nat.cast_nonneg _
  have hcross : (0 : ℝ) ≤ Fintype.card G * (Fintype.card I + 1) := by positivity
  have hbase : 1 ≤ base := by dsimp only [base]; linarith only [hI, hG, hcross, hR]
  have hRbase : R ≤ base := by dsimp only [base]; linarith only [hI, hG, hcross]
  have hcube : base ≤ base ^ 3 := le_self_pow₀ hbase (by norm_num)
  have hproduct : (0 : ℝ) ≤ (Fintype.card G : ℝ) *
      (Fintype.card I + 1) * Fintype.card I := by positivity
  have hfactor : (1 : ℝ) ≤ 4 + 3 * ((Fintype.card G : ℝ) *
      (Fintype.card I + 1) * Fintype.card I) := by linarith only [hproduct]
  have hinner : 0 ≤ 16 * base ^ 3 + 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hfactor hinner
  rw [scalarKernelLogarithmicBudget_eq]
  change R ≤ 2 * ((4 + 3 * ((Fintype.card G : ℝ) *
    (Fintype.card I + 1) * Fintype.card I)) * (16 * base ^ 3 + 2)) + 8
  linarith only [hRbase, hcube, hmul, hbase]

theorem preparedFiniteForwardPairedSourcePrecision_gain_lower
    (A Cdirect : ℕ) (constants : ℕ → ℕ) (stage : ℕ) (direct : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    gainLog ≤ preparedFiniteForwardPairedSourcePrecision A Cdirect constants stage direct
      x gainLog stageLog := by
  have hsource := preparedFiniteForwardPairedSourcePrecision_model_lower
    A Cdirect constants stage direct hx hg hs
  have hprefix := (preparedFiniteForward_prefix_bounds A constants stage hx).2.1
  have hwork := preparedFiniteForwardWork_nonneg A constants stage hx
  dsimp only [preparedFiniteForwardModelPrecision] at hsource
  linarith only [hsource, hprefix, hwork, hs.1]

theorem preparedFiniteScheduleLocalPhysical_gain
    (m nX count degree Cdetect : ℕ) (G : Type*) [Fintype G]
    {u pModel gainLog Qstride : ℝ}
    (hu : 0 ≤ u) (hmodel : 0 ≤ pModel) (hgain : gainLog ≤ u) (hstride : 0 ≤ Qstride) :
    let pDetect := allocatedModelTestLog u pModel
    let pGain := slicedDetectionGainLog degree Cdetect count pDetect pDetect
      (2 * u + 4 * pModel + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G (pGain + pDetect + 4)
    gainLog + (nX : ℝ) + 8 ≤ preparedFiniteScheduleLocalPhysical m nX count Qstride Pk := by
  intro pDetect pGain Pk
  have hdetect : 0 ≤ pDetect := by dsimp only [pDetect, allocatedModelTestLog]; positivity
  have hgainDetect : 0 ≤ pGain := slicedDetectionGainLog_nonneg degree Cdetect count
    hdetect hdetect (by positivity)
  have hinput : 0 ≤ pGain + pDetect + 4 := by positivity
  have hkernel := preparedFiniteSchedule_kernel_input_le (Fin (degree + 1)) G hinput
  have hm : (0 : ℝ) ≤ (m + 2 : ℕ) := Nat.cast_nonneg _
  have hcount : (0 : ℝ) ≤ count := Nat.cast_nonneg _
  change pGain + pDetect + 4 ≤ Pk at hkernel
  dsimp only [preparedFiniteScheduleLocalPhysical]
  dsimp only [pDetect, allocatedModelTestLog] at hkernel
  linarith only [hkernel, hm, hcount, hgainDetect, hgain, hu, hmodel, hstride]

theorem preparedFiniteScheduleLocalPhysical_tau_inv
    (m nX count degree Cdetect : ℕ) (G : Type*) [Fintype G]
    {u pModel gainLog Qstride : ℝ}
    (hu : 0 ≤ u) (hmodel : 0 ≤ pModel) (hgain : gainLog ≤ u) (hstride : 0 ≤ Qstride) :
    let pDetect := allocatedModelTestLog u pModel
    let pGain := slicedDetectionGainLog degree Cdetect count pDetect pDetect
      (2 * u + 4 * pModel + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G (pGain + pDetect + 4)
    (Real.exp (-(gainLog + (nX : ℝ) + 8)))⁻¹ ≤
      Real.exp (preparedFiniteScheduleLocalPhysical m nX count Qstride Pk) := by
  intro pDetect pGain Pk
  rw [Real.exp_neg, inv_inv]
  exact Real.exp_le_exp.mpr (preparedFiniteScheduleLocalPhysical_gain
    m nX count degree Cdetect G hu hmodel hgain hstride)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ} (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (τ u p forecastCap : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]

variable (Good : ∀ (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ)),
  (∀ j ex, coefficients (poly j) ex ∈ U j) →
  ∀ (width : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)),
    (CoefficientTorus (K := LayerSamplerVariables G I n B) U →
      FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) → Prop)

variable (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget extraRequired : ℝ)
local notation "r" => preparedModularGeneralDetectorResources
  (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate
local notation "Ctail" =>
  (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap

theorem allocatedExternalCandidatePreparedGood_of_model
    (hGoodModel : SharedWidthPreparedCenteredForecastModelExtensionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ) (Good := Good)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget extraRequired)
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
    {E : ℝ}
    (hτ : 0 < τ) (hτInv : τ⁻¹ ≤ Real.exp Pphysical)
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff 0 G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog uSource pModel) (allocatedModelTestLog uSource pModel) (α / 2))
      Pphysical coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ i, Real.exp (max
      (max (r).required ((max (r).Pproj E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m)) extraRequired) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : Real.exp (max
      (max (r).required ((max (r).Pproj E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m)) extraRequired) ≤ Rrank)
    (hCells : cells.Nonempty)
    (A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hmem τ ξ stride cells) :
    (∀ z, Measurable (fun center => (A.law center).weight z)) ∧
      Good poly hmem (allocatedExternalCandidateWidths B U basis S N τ ξ) (A 0).bases A.law := by
  obtain ⟨hN, hbases, _hbox, hmass, _hnormalizer, _hmargin,
      hnormalizerCenter, hweight, hGood, _hmodel⟩ :=
    hGoodModel hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff hτ hτInv hτHalf hτDim hξ hξSmall hξLate
      cells poly hp hmem hsize hrank hRank hCells
  exact A.measurable_good_of_prepared hbases
    (narrowTrimmedSpatialWidths_pos (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
      hτ hξ N hN)
    hmass (fun center => (hnormalizerCenter center).2.2.1) (Good poly hmem) hweight hGood

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedScalarFiniteScheduleLocalPhysical_model_add
    (q nX count degree Cdetect : ℕ) (G : Type*) [Fintype G]
    {sourceU modelLog : ℝ} (hsource : 0 ≤ sourceU) (hmodel : 0 ≤ modelLog) :
    let pDetect := allocatedModelTestLog sourceU modelLog
    let pGain := slicedDetectionGainLog degree Cdetect count pDetect pDetect
      (2 * sourceU + 4 * modelLog + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
      (pGain + pDetect + 4)
    modelLog + (nX : ℝ) + 8 ≤ preparedFiniteScheduleLocalPhysical q nX count 0 Pk := by
  intro pDetect pGain Pk
  have hdetect : 0 ≤ pDetect := by
    dsimp only [pDetect, allocatedModelTestLog]
    positivity
  have hgain : 0 ≤ pGain := slicedDetectionGainLog_nonneg degree Cdetect count
    hdetect hdetect (by positivity)
  have hinput : 0 ≤ pGain + pDetect + 4 := by positivity
  have hkernel := preparedFiniteSchedule_kernel_input_le (Fin (degree + 1)) G hinput
  change pGain + pDetect + 4 ≤ Pk at hkernel
  have hq : (0 : ℝ) ≤ (q + 2 : ℕ) := Nat.cast_nonneg _
  have hcount : (0 : ℝ) ≤ count := Nat.cast_nonneg _
  dsimp only [preparedFiniteScheduleLocalPhysical]
  dsimp only [pDetect, allocatedModelTestLog] at hkernel
  linarith only [hkernel, hgain, hq, hcount, hsource, hmodel]

theorem preparedScalarFiniteScheduleLocalPhysical_model
    (q nX count degree Cdetect : ℕ) (G : Type*) [Fintype G]
    {sourceU modelLog : ℝ} (hsource : 0 ≤ sourceU) (hmodel : 0 ≤ modelLog) :
    let pDetect := allocatedModelTestLog sourceU modelLog
    let pGain := slicedDetectionGainLog degree Cdetect count pDetect pDetect
      (2 * sourceU + 4 * modelLog + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
      (pGain + pDetect + 4)
    modelLog ≤ preparedFiniteScheduleLocalPhysical q nX count 0 Pk := by
  intro pDetect pGain Pk
  have h := preparedScalarFiniteScheduleLocalPhysical_model_add
    q nX count degree Cdetect G hsource hmodel
  change modelLog + (nX : ℝ) + 8 ≤
    preparedFiniteScheduleLocalPhysical q nX count 0 Pk at h
  have hnX : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
  linarith only [h, hnX]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForwardWork_cubic_lower
    (A : ℕ) (constants : ℕ → ℕ) (stage : ℕ) {p seed : ℝ}
    (hp : 2 ≤ p) (hA : 3 ≤ A) (hseed : p ≤ seed) :
    (p + 2) ^ 3 ≤ preparedFiniteForwardWork A constants stage seed := by
  have hseed0 : 0 ≤ seed := by linarith
  have hparam := le_preparedFiniteForwardParameter A constants stage hseed0
  have hAreal : (3 : ℝ) ≤ A := by exact_mod_cast hA
  rw [preparedFiniteForwardWork_eq]
  calc
    (p + 2) ^ 3 ≤ (preparedFiniteForwardParameter A constants stage seed + A) ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 3
    _ ≤ _ := pow_le_pow_right₀ (by linarith) hA

theorem preparedScalarFiniteScheduleLocalPhysical_exp_trim
    (q nX count degree Cdetect A stage : ℕ) (G : Type*) [Fintype G]
    (constants : ℕ → ℕ) {p seed sourceU : ℝ}
    (hp : 2 ≤ p) (hX : (nX : ℝ) ≤ p) (hA : 3 ≤ A)
    (hseed : p ≤ seed) (hsource : 0 ≤ sourceU) :
    let modelLog := preparedFiniteForwardWork A constants stage seed
    let pDetect := allocatedModelTestLog sourceU modelLog
    let gain := slicedDetectionGainLog degree Cdetect count pDetect pDetect
      (2 * sourceU + 4 * modelLog + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G (gain + pDetect + 4)
    let τ := unconditionedSpatialTrimFraction nX (Real.exp (-p))
    τ⁻¹ ≤ Real.exp (preparedFiniteScheduleLocalPhysical q nX count 0 Pk) ∧
      τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 := by
  intro modelLog pDetect gain Pk τ
  obtain ⟨_, hhalf, hdim, hinv⟩ := unconditionedSpatialTrimFraction_exp_bounds hp hX
  have hmodel : 0 ≤ modelLog :=
    preparedFiniteForwardWork_nonneg A constants stage (by linarith)
  have hdom : modelLog ≤ preparedFiniteScheduleLocalPhysical q nX count 0 Pk :=
    preparedScalarFiniteScheduleLocalPhysical_model q nX count degree Cdetect G hsource hmodel
  refine ⟨hinv.trans (Real.exp_le_exp.mpr (?_)), hhalf, hdim⟩
  exact (preparedFiniteForwardWork_cubic_lower A constants stage hp hA hseed).trans hdom

theorem preparedScalarFiniteScheduleLocalPhysical_nested_exp_trim
    (q nX count degree Cdetect A stage innerDepth outer : ℕ)
    (G : Type*) [Fintype G] (constants : ℕ → ℕ)
    {p Bstruct sourceU : ℝ}
    (hp : 2 ≤ p) (hX : (nX : ℝ) ≤ p) (hA : 3 ≤ A)
    (hB : p ≤ Bstruct) (hsource : 0 ≤ sourceU) :
    let seed := candidateNestedForwardSeed A constants innerDepth outer Bstruct
    let modelLog := preparedFiniteForwardWork A constants stage seed
    let pDetect := allocatedModelTestLog sourceU modelLog
    let gain := slicedDetectionGainLog degree Cdetect count pDetect pDetect
      (2 * sourceU + 4 * modelLog + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G (gain + pDetect + 4)
    let τ := unconditionedSpatialTrimFraction nX (Real.exp (-p))
    τ⁻¹ ≤ Real.exp (preparedFiniteScheduleLocalPhysical q nX count 0 Pk) ∧
      τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 := by
  apply preparedScalarFiniteScheduleLocalPhysical_exp_trim
    q nX count degree Cdetect A stage G constants hp hX hA
  · exact hB.trans (le_candidateNestedForwardSeed A constants innerDepth outer
      (by omega) (by linarith))
  · exact hsource

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}

theorem allocatedExternalPreparedProductiveCenter_of_model
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (B0 gainLog gain Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (Pprod : ℝ)
    (hGoodModel : SharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface
      prep U b hR hσ S selection stride N Pdetect uSource pModel pSlice
      Vtail τ u p forecastCap hb o bW μ
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      B0 gainLog gain Pgood Qgood spatialEmbedding Pprod)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    {E : ℝ}
    (hτ : 0 < τ) (hτInv : τ⁻¹ ≤ Real.exp Pphysical)
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selection
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog uSource pModel) (allocatedModelTestLog uSource pModel) (forecastAugmentedUnitThreshold u p (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))) (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastCap / 2))
      Pphysical coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ i, Real.exp (max
      (max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate)).required ((max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate)).Pproj E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m)) (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
        ((Pprod + preparedModularGeneralProductivityExponent m) ^
          preparedModularGeneralProductivityExponent m))) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : Real.exp (max
      (max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate)).required ((max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate)).Pproj E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m)) (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
        ((Pprod + preparedModularGeneralProductivityExponent m) ^
          preparedModularGeneralProductivityExponent m))) ≤ Rrank)
    (hCells : cells.Nonempty)
    (A : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S hb o hR hσ
      N poly hmem τ ξ stride cells)
    (test : (Fin nX → ℝ) → ℝ)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) :
    PreparedCenteredProductiveGoodCenterConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hmem stride
      (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N τ ξ) (A 0).bases
      gainLog gain Qgood spatialEmbedding A.law N test := by
  obtain ⟨hweight, hgood, hproductive⟩ :=
    allocatedExternalCandidatePreparedGood_of_model
      (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ) (Good := _)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
        ((Pprod + preparedModularGeneralProductivityExponent m) ^
          preparedModularGeneralProductivityExponent m)) hGoodModel
      hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff hτ hτInv hτHalf hτDim hξ hξSmall hξLate
      cells poly hp hmem hsize hrank hRank hCells A
  exact preparedCenteredProductiveGoodCenter (m := m) (nX := nX) (M := M)
    prep U b S bW hb o hR hσ μ poly hmem stride
    (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N τ ξ) (A 0).bases
    gainLog gain Qgood spatialEmbedding A.law N test hweight hgood hproductive htest hgain hmean

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}
variable (prep : RankPreparationFamily X₀ J₀ m)
noncomputable local instance productiveFixedSourceFinDecidableEq : DecidableEq (Fin nX) := Classical.decEq _
variable (U : ∀ j, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
variable (basis : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U basis R σ)
variable {Stage : Type} (degree : Stage → ℕ)
variable (selection : ∀ k, Fin (degree k + 1) ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
variable (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable (sourceU modelLog sliceLog α : Stage → ℝ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]

theorem exists_preparedFiniteScheduleProductiveFixedCenterSource
    (kAnchor : Stage)
    (Pchart Qstride : ℝ) (Pmaster : Stage → ℝ) (Plate : ℝ)
    (Pphysical : Stage → ℝ) (coarseTarget : ℝ) (pGain : Stage → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDirectSourceAvailability
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {Pscale D target Pk Prho pRadius E : ℝ}
    (scalar : PreparedUniformDegreeDirectScalarBounds m (degree kAnchor) nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
      (sampledSupportedSlicedDetectionConstant (degree kAnchor) Pdetect)
      Pchart Pscale D target Pk Prho Qstride (Pmaster kAnchor) Plate (pGain kAnchor)
      (Pphysical kAnchor) coarseTarget pRadius (sourceU kAnchor) (modelLog kAnchor) (sliceLog kAnchor))
    (geometryAt : PreparedUniformDegreeGeometryAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U basis S (degree kAnchor)
      (sampledSupportedSlicedDetectionConstant (degree kAnchor) Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog (sourceU kAnchor) (modelLog kAnchor))
      pRadius (2 * sourceU kAnchor + 4 * modelLog kAnchor + 7) (pGain kAnchor))
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
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
    (hτ : 0 < τ) (hτInv : ∀ k, τ⁻¹ ≤ Real.exp (Pphysical k))
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ∀ k, ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) (selection k)
      (allocatedDetectedKernelCutoff (degree k) (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog (sourceU k) (modelLog k))
        (allocatedModelTestLog (sourceU k) (modelLog k)) (α k / 2))
      (Pphysical k) coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ k i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : ∀ k, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ Rrank)
    (hsizeConditional : ∀ i, Real.exp (preparedConditionalExcessRequired m Plate E) ≤ (N i : ℝ))
    (hRankConditional : Real.exp (preparedConditionalExcessRequired m Plate E) ≤ Rrank)
    (hCells : cells.Nonempty)
    (hdimension : ∀ k, (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
    (selectionProductive : Fin (0 + 1) ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    (sourceProductive modelProductive sliceProductive uProductive pProductive forecastProductive : ℝ)
    (PmasterProductive pGainProductive PphysicalProductive : ℝ)
    (B0 gainLog gain Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (Pprod : ℝ)
    (hProductiveSource : SharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface
      prep U basis hR hσ S selectionProductive stride N Pdetect sourceProductive modelProductive sliceProductive
      Vtail τ uProductive pProductive forecastProductive hb o bW μ
      Pchart Qstride PmasterProductive Plate pGainProductive PphysicalProductive coarseTarget
      B0 gainLog gain Pgood Qgood spatialEmbedding Pprod)
    (hτInvProductive : τ⁻¹ ≤ Real.exp PphysicalProductive)
    (hξSmallProductive : ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selectionProductive
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog sourceProductive modelProductive) (allocatedModelTestLog sourceProductive modelProductive) (forecastAugmentedUnitThreshold uProductive pProductive (Real.exp (sliceProductive * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))) (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastProductive / 2))
      PphysicalProductive coarseTarget)
    (hsizeProductive : ∀ i, Real.exp (max
      (max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) PmasterProductive Plate)).required ((max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) PmasterProductive Plate)).Pproj E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m)) (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
        ((Pprod + preparedModularGeneralProductivityExponent m) ^
          preparedModularGeneralProductivityExponent m))) ≤ (N i : ℝ))
    (hRankProductive : Real.exp (max
      (max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) PmasterProductive Plate)).required ((max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) PmasterProductive Plate)).Pproj E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m)) (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
        ((Pprod + preparedModularGeneralProductivityExponent m) ^
          preparedModularGeneralProductivityExponent m))) ≤ Rrank)
    (test : (Fin nX → ℝ) → ℝ)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ)))
    : ∃ hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i,
    ∃ A : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U basis S hb o hR hσ N poly hmem τ ξ stride cells,
      PreparedCenteredProductiveGoodCenterReadyConclusion (m := m) (nX := nX) (M := M)
        prep U basis S bW hb o hR hσ μ poly hmem stride
        (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U basis S N τ ξ) (A 0).bases
        gainLog gain Qgood spatialEmbedding A.law N test (fun center =>
    (∀ k, (A center).NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k)) ∧
      letI : Nonempty (A center).Site := (A center).site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) (A center).integerBox_nonempty).excessMass
        ((A center).law.siteLaw ((A center).physicalBox
          ((hξSmall kAnchor).trans (min_le_left _ _)) hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j)) ≤
          6 * positiveProjectionAccuracy E) := by
  obtain ⟨hmargin, A, hdetect, hexcess⟩ :=
    exists_preparedFiniteScheduleFixedCenterSource
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
      (degree := degree) (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU) (modelLog := modelLog) (sliceLog := sliceLog)
      (α := α) (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      kAnchor Pchart Qstride Pmaster Plate Pphysical coarseTarget pGain hAvailable μ ν
      scalar geometryAt hSLate hαLower hαHalfOne hstride hstrideBound
      C hC hCbound hchart Cforward hforward hForward hVtail hVactual hprofile hcutoff
      hτ hτInv hτHalf hτDim hξ hξSmall hξLate cells poly hp hmem hsize hrank hRank
      hsizeConditional hRankConditional hCells hdimension
  have hdec : productiveFixedSourceFinDecidableEq = instDecidableEqFin nX := Subsingleton.elim _ _
  have hmeanProductive := hmean
  rw [hdec] at hmeanProductive
  have hselected := allocatedExternalPreparedProductiveCenter_of_model
    (m := m) (nX := nX) (M := M) prep U basis hR hσ S selectionProductive stride N Pdetect
    sourceProductive modelProductive sliceProductive Vtail τ uProductive pProductive forecastProductive
    hb o bW μ Pchart Qstride PmasterProductive Plate pGainProductive PphysicalProductive coarseTarget
    B0 gainLog gain Pgood Qgood spatialEmbedding Pprod hProductiveSource
    hstride hstrideBound C hC hCbound hchart Cforward hforward hForward hVtail hVactual hprofile hcutoff
    hτ hτInvProductive hτHalf hτDim hξ hξSmallProductive hξLate cells poly hp hmem
    hsizeProductive hrank hRankProductive hCells A test htest hgain hmeanProductive
  refine ⟨hmargin, A, ?_⟩
  apply preparedCenteredProductiveGoodCenter_with_ready
    (m := m) (nX := nX) (M := M) prep U basis S bW hb o hR hσ μ poly hmem stride
    (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U basis S N τ ξ) (A 0).bases
    gainLog gain Qgood spatialEmbedding A.law N test _ hselected
  intro center
  exact ⟨fun k => hdetect k center, hexcess center⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
variable {nX : ℕ}
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

theorem exists_preparedFiniteNestedForwardProductiveFixedCenterSource
    {m M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m) (outerDepth innerDepth cutoff : ℕ)
    [∀ j : Fin (max m cutoff), DecidableEq (RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))]
    (U : ∀ j, Submodule ℝ ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse (prep.pad (max m cutoff))) j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ)
    (Vtail : Fin (max m cutoff) → ℝ≥0)

    (Q : Fin (max m cutoff) → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

    (A Cslice Cdirect : ℕ) (stageCountConstant : ℕ → ℕ)
    (hA : 2 ≤ A) (hSliceExponent : Cslice + 1 ≤ A)
    (Bstruct Qstride forecastCap stageLog Econditional : ℝ)
    (Qσ Qw Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < max m cutoff) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hQstride : 0 ≤ Qstride)
    (hQσ : 0 ≤ Qσ) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin (max m cutoff) → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Bstruct)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin (max m cutoff) → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Bstruct)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Bstruct)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) (Fin nX) stride))
    (hCells : cells.Nonempty)
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (Rrank : ℝ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (test : (Fin nX → ℝ) → ℝ) (htest : ∀ x, |test x| ≤ 1)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) :
    let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
    let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
    let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
    let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let kModel : K := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff
    let sourceU := fun k : K =>
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
        (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog
    let modelLog := fun k : K => preparedFiniteForwardWork A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k)
    let sliceLog := fun k : K =>
      (preparedFiniteForwardParameter A stageCountConstant (preparedFiniteNestedForwardAllDegreeStage k).val
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) + Cslice) ^ Cslice
    let u := preparedFiniteForwardModelPrecision A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct) gainLog stageLog
    let p := preparedFiniteForwardWork A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct)
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension (max m cutoff) M (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))
    let R : Fin (max m cutoff) → ℝ := fun _ => allocatedCommonProductRadius (max m cutoff) Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog (max m cutoff) Bstruct Bstruct
    let D := allocatedComparisonDimension (max m cutoff) pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical (max m cutoff) nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun s : K => target s + D * (((max m cutoff) * 2 ^ ((max m cutoff) + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope (max m cutoff) D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => (((max m cutoff) + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog (max m cutoff) D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) * (nX + (max m cutoff) * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let α := fun k : K => Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog +
      4 * modelLog k + 8))
    let baseB0 := preparedUniformDegreeProductiveCertificateBudget M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
    let Pwidth := 4 * (Plate + 8) ^ 2
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Bstruct Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent (max m cutoff))
      baseB0 Bstruct Pwidth gainLog Vlog
    let anchorRequired := preparedFiniteScheduleAnchorGoodRequired (max m cutoff) (Pmaster kModel) Plate Econditional Bcert Pgood Pwidth
    let conditionalRequired := preparedConditionalExcessRequired (max m cutoff) Plate Econditional
    let detectorRequired := fun k : K => (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants (max m cutoff) (degree k)) (degree k + 1) (Pmaster k) Plate).required
    let Rreq := preparedFiniteNestedSourceRequired A stageCountConstant innerDepth outerDepth cutoff Bstruct
      anchorRequired conditionalRequired detectorRequired
    pnum ≤ Bstruct →
    W ≤ Real.exp Qw →
    (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j)) ≤ Real.exp p →
    0 ≤ forecastCap → forecastCap ≤ Real.exp p →
    (∀ i, Real.exp Rreq ≤ (N i : ℝ)) → Real.exp Rreq ≤ Rrank →
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) («I» := (PreparedSamplerContinuous (prep.pad (max m cutoff)))) («n» := (preparedSamplerTransverse (prep.pad (max m cutoff)))) («J» := (fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds (max m cutoff) (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff)))
          (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k) (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, PreparedScheduledDegreeModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k)
              (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := (max m cutoff)) (nX := nX) (M := M) (prep := (prep.pad (max m cutoff))) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood ∧
      ∃ (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
        (Acandidate : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S hb o hR (fun _ => hσ)
          N poly hmem τ (Real.exp (-Plate)) stride cells)
        (hξone : Real.exp (-Plate) ≤ 1),
      PreparedCenteredProductiveGoodCenterReadyConclusion (m := (max m cutoff)) (nX := nX) (M := M)
        (prep.pad (max m cutoff)) U b S bW hb o hR (fun _ => hσ) μ poly hmem stride
        (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S N τ (Real.exp (-Plate))) (Acandidate 0).bases
        gainLog gain Qgood (preparedSpatialKernelBlocks (max m cutoff) M nX) Acandidate.law N test
        (fun center =>
          letI : DecidableEq (Fin nX) := Classical.decEq _
          (∀ k : K, (Acandidate center).NativeDetection (degree k) (sliceLog k)
            (Pdetect.eval₂ (Nat.castRingHom ℝ) (pDetect k))
            (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants (max m cutoff) (degree k))
              (degree k + 1) (Pmaster k) Plate).nativeBudget (α k)) ∧
          letI : Nonempty (Acandidate center).Site := (Acandidate center).site_nonempty
          (FiniteProbabilityWeights.uniformFinset (integerBox N) (Acandidate center).integerBox_nonempty).excessMass
            ((Acandidate center).law.siteLaw ((Acandidate center).physicalBox hξone hmargin))
            (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j)) ≤
              6 * positiveProjectionAccuracy Econditional) := by
  intro Pdetect K degree Cdetect kModel sourceU modelLog sliceLog u p
    pnum R pRadius D pDetect aDetect detectionGain Pk Pphysical target E Prho Ptail Pscale Tmod
    lengthLogs Pseed W Pmaster coarseTarget Plate τ α baseB0 Pwidth Bcert Pgood
    anchorRequired conditionalRequired detectorRequired Rreq hnum hWexp hCtail hForecastCap hForecastCapP
    hNrequired hRankRequired
  have sourceResult :
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) («I» := (PreparedSamplerContinuous (prep.pad (max m cutoff)))) («n» := (preparedSamplerTransverse (prep.pad (max m cutoff)))) («J» := (fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds (max m cutoff) (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff)))
          (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k) (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, PreparedScheduledDegreeModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k)
              (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := (max m cutoff)) (nX := nX) (M := M) (prep := (prep.pad (max m cutoff))) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood := by
    exact exists_preparedFiniteNestedForwardAllDegreePaddedProductiveSource
      prep outerDepth innerDepth cutoff U b stride N Pdetect Vtail Q hb o bW ν μ μrows
      A Cslice Cdirect stageCountConstant hA hSliceExponent Bstruct Qstride forecastCap stageLog
      Qσ Qw Pmin requestedCoarse gainLog gain Vlog Lmin Qgood hm hnX hCoord hB hstage
      hQstride hQσ hQw hPmin hLmin hg hVlog hQgood hQexp hgain hnChart hgChart
      hnum hWexp hCtail hForecastCap hForecastCapP
  obtain ⟨hR, σ, hσ, S, hRadius, hRbounds, hσone, hσexp, hσinv, hFloor,
    hS, hgap, hgeometry, hscalar, hdirect, hdegreeModel, hproductive⟩ :=
    sourceResult
  have hseedLower (k : K) : Bstruct ≤ preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k :=
    le_preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant hA hB k
  have hseed (k : K) : 0 ≤ preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k := hB.trans (hseedLower k)
  have hseedGain (k : K) : gainLog ∈ Set.Icc 0 (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) :=
    ⟨hg, hgChart.trans (hseedLower k)⟩
  have hseedStage (k : K) : stageLog ∈ Set.Icc 0 (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) :=
    ⟨hstage.1, hstage.2.trans (hseedLower k)⟩
  have hαLower (k : K) : Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2 :=
    preparedFiniteForwardFixedCenterThreshold_lower A Cdirect stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
      (hseed k) (hseedGain k) (hseedStage k)
  have hαHalfOne (k : K) : α k / 2 ≤ 1 :=
    preparedFiniteForwardFixedCenterThreshold_half_le_one A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val (hseed k) (hseedGain k) (hseedStage k)
  let selection := (fun k : K => enlargedPreparedCommonCanonicalSelection (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k) (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
  have hξSmall (k : K) := preparedFiniteScheduleDirectWidth
    (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S (selection k) Pdetect (Cdetect k) rfl
    Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
    (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)
    (α k / 2) (hscalar k) (hgeometry k) (hαLower k)
  have hξ : 0 < Real.exp (-Plate) := Real.exp_pos _
  have hξLate : (Real.exp (-Plate))⁻¹ ≤ Real.exp Plate := by simp only [Real.exp_neg, inv_inv, le_refl]
  have hξone : Real.exp (-Plate) ≤ 1 := sharedWidthPreparedChoice_le_one
    ((hscalar kModel).master_nonneg.trans (hscalar kModel).late)
  have hSLate : (S.value : ℝ) ≤ Real.exp Plate := by
    exact hS.trans (Real.exp_le_exp.mpr (preparedFiniteScheduleDirectLate_extra_le_sum
      kModel Pmaster Pphysical Pscale coarseTarget (allocatedWitnessScaleLog Pseed Qw)
      (fun k => (hscalar k).master_nonneg)))
  obtain ⟨_, hτ, hτHalf, hτDim, _, hτBudget, _⟩ := preparedEarlySpatialWidth nX hg
  have hτInv (k : K) : τ⁻¹ ≤ Real.exp (Pphysical k) := by
    apply hτBudget
    exact preparedFiniteScheduleLocalPhysical_gain (max m cutoff) nX (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))
      (degree k) (Cdetect k)
      (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
      (hscalar k).u_master.1 (hscalar k).model_master.1
      (preparedFiniteForwardPairedSourcePrecision_gain_lower A Cdirect stageCountConstant
        (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (hseed k) (hseedGain k) (hseedStage k)) hQstride
  have hcount : ((Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) : ℝ) ≤ Bstruct :=
    (Nat.cast_le.mpr (enlargedPreparedCommonSampler_dimensions (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))
      (prep.pad_coordinate_card_le hCoord)).1).trans hnum
  have hdimension (k : K) : ((Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (pDetect k) := by
    have hwork := preparedFiniteForward_shiftedPower_le_work A 1 stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val hA (by omega : 1 ≤ A) (hseed k)
    have hseedWork : preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k ≤ modelLog k := by
      have := hwork
      simp only [pow_one, Nat.cast_one] at this
      linarith only [this]
    exact (hcount.trans (hseedLower k)).trans (hseedWork.trans
      (preparedFiniteForwardDetectorPolynomial_stage_bounds cutoff A Cdirect stageCountConstant
        (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (hseed k) (hseedGain k) (hseedStage k)).1)
  have hu : 0 ≤ u := (preparedFiniteForward_model_precision_bounds A stageCountConstant innerDepth
    (hseed kModel) (hseedGain kModel) (hseedStage kModel)).1
  have hpModel : 0 ≤ p := (hscalar kModel).model_master.1
  have hsourceModel : sourceU kModel = u + 2 * p + 1 := by
    change preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant innerDepth false
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct) gainLog stageLog = _
    rw [preparedFiniteForwardPairedSourcePrecision_model]
    rfl
  have hsliceModel : sliceLog kModel * (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) ≤ p :=
    (preparedFiniteForward_controlled_slice_bounds A Cslice stageCountConstant innerDepth (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))
      hA hSliceExponent (hseed kModel) (hcount.trans (hseedLower kModel))).2.2
  have hmodel := hdegreeModel kModel u p forecastCap hsourceModel hu hpModel hsliceModel hCtail hForecastCap hForecastCapP
  rw [hsourceModel] at hmodel
  have hξProductive := (sharedWidthNormalizedTuplePreparedChoice
    (fun _ : Unit => 1)
    (fun _ => allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) Pdetect
      (allocatedModelTestLog (u + 2 * p + 1) (modelLog kModel))
      (allocatedModelTestLog (u + 2 * p + 1) (modelLog kModel))
      (forecastAugmentedUnitThreshold u p (Real.exp (sliceLog kModel * (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))))
        (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j))) forecastCap / 2))
    (fun _ => enlargedPreparedCommonCanonicalSelection (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) 0 (Nat.zero_le _))
    (fun _ => Pphysical kModel) (fun _ => coarseTarget) Plate
    (fun _ => hmodel.2)).2.2 ()
  obtain ⟨⟨hGoodSize, hGoodRank⟩, ⟨hConditionalSize, hConditionalRank⟩, hDirectFloors, _⟩ :=
    preparedFiniteNestedSourceRequired_size_rank A stageCountConstant innerDepth outerDepth cutoff Bstruct
      anchorRequired conditionalRequired detectorRequired N Rrank hNrequired hRankRequired
  obtain ⟨hmargin, Acandidate, hready⟩ :=
    exists_preparedFiniteScheduleProductiveFixedCenterSource
      (m := (max m cutoff)) (nX := nX) (M := M) (prep := (prep.pad (max m cutoff))) (E := Econditional)
      (U := U) (basis := b) (hR := hR) (hσ := fun _ => hσ) (S := S)
      (degree := degree) (selection := selection) (stride := stride) (N := N) (Pdetect := Pdetect)
      (sourceU := sourceU) (modelLog := modelLog) (sliceLog := sliceLog) (α := α)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (bW := bW)
      kModel Bstruct Qstride Pmaster Plate Pphysical coarseTarget detectionGain
      (fun k => preparedScheduledDirectSourceAvailability_decidableTransport (hdirect k)) μ ν
      (hscalar kModel) (preparedUniformDegreeGeometryAt_decidableTransport (hgeometry kModel)) hSLate hαLower hαHalfOne hstride hstrideBound
      C hC hCbound hchart Cforward hforward hForward hVtail hVactual hprofile hcutoff
      hτ hτInv hτHalf hτDim hξ hξSmall hξLate cells poly hp hmem
      (fun k => (hDirectFloors k).1) hrank (fun k => (hDirectFloors k).2)
      hConditionalSize hConditionalRank hCells hdimension
      (enlargedPreparedCommonCanonicalSelection (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) 0 (Nat.zero_le _))
      (u + 2 * p + 1) (modelLog kModel) (sliceLog kModel) u p forecastCap
      (Pmaster kModel) (detectionGain kModel) (Pphysical kModel)
      Bcert gainLog gain Pgood Qgood (preparedSpatialKernelBlocks (max m cutoff) M nX) Pwidth
      hproductive (hτInv kModel) hξProductive hGoodSize hGoodRank test htest hgain
      (by
        have hdec : productiveFixedSourceFinDecidableEq (nX := nX) = instDecidableEqFin nX :=
          Subsingleton.elim _ _
        rw [hdec]
        exact hmean)
  exact ⟨hR, σ, hσ, S, hRadius, hRbounds, hσone, hσexp, hσinv, hFloor,
    hS, hgap, hgeometry, hscalar, hdirect, hdegreeModel, hproductive,
    hmargin, Acandidate, hξone, hready⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
variable {nX : ℕ}
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

theorem exists_preparedFiniteNestedForwardCanonicalFixedCenterSource
    {m M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m) (outerDepth innerDepth cutoff : ℕ)
    [∀ j : Fin (max m cutoff), DecidableEq (RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))]
    (U : ∀ j, Submodule ℝ ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse (prep.pad (max m cutoff))) j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ)
    (Vtail : Fin (max m cutoff) → ℝ≥0)

    (Q : Fin (max m cutoff) → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

    (e Cprimitive Cdirect extra : ℕ) (stageCountConstant : ℕ → ℕ)
    (Bstruct Qstride stageLog Econditional : ℝ)
    (Qσ Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < max m cutoff) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hQstride : 0 ≤ Qstride)
    (hQσ : 0 ≤ Qσ) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin (max m cutoff) → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Bstruct)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin (max m cutoff) → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Bstruct)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Bstruct)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) (Fin nX) stride))
    (hCells : cells.Nonempty)
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (Rrank : ℝ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (test : (Fin nX → ℝ) → ℝ) (htest : ∀ x, |test x| ≤ 1)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) :
    let A := preparedFiniteNestedSourceExponent (max m cutoff) cutoff e Cprimitive Cdirect extra
    let Cslice := preparedFiniteNestedSourceSliceExponent (max m cutoff) cutoff Cprimitive
    let forecastCap : ℝ := 1
    let Qw := 2 * Bstruct + 2 * Vlog + 5 * (gainLog + 8) + 24
    let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
    let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
    let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
    let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let kModel : K := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff
    let sourceU := fun k : K =>
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
        (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog
    let modelLog := fun k : K => preparedFiniteForwardWork A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k)
    let sliceLog := fun k : K =>
      (preparedFiniteForwardParameter A stageCountConstant (preparedFiniteNestedForwardAllDegreeStage k).val
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) + Cslice) ^ Cslice
    let u := preparedFiniteForwardModelPrecision A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct) gainLog stageLog
    let p := preparedFiniteForwardWork A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct)
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension (max m cutoff) M (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))
    let R : Fin (max m cutoff) → ℝ := fun _ => allocatedCommonProductRadius (max m cutoff) Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog (max m cutoff) Bstruct Bstruct
    let D := allocatedComparisonDimension (max m cutoff) pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical (max m cutoff) nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun s : K => target s + D * (((max m cutoff) * 2 ^ ((max m cutoff) + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope (max m cutoff) D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => (((max m cutoff) + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog (max m cutoff) D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) * (nX + (max m cutoff) * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let α := fun k : K => Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog +
      4 * modelLog k + 8))
    let baseB0 := preparedUniformDegreeProductiveCertificateBudget M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
    let Pwidth := 4 * (Plate + 8) ^ 2
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Bstruct Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent (max m cutoff))
      baseB0 Bstruct Pwidth gainLog Vlog
    let anchorRequired := preparedFiniteScheduleAnchorGoodRequired (max m cutoff) (Pmaster kModel) Plate Econditional Bcert Pgood Pwidth
    let conditionalRequired := preparedConditionalExcessRequired (max m cutoff) Plate Econditional
    let detectorRequired := fun k : K => (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants (max m cutoff) (degree k)) (degree k + 1) (Pmaster k) Plate).required
    let Rreq := preparedFiniteNestedSourceRequired A stageCountConstant innerDepth outerDepth cutoff Bstruct
      anchorRequired conditionalRequired detectorRequired
    pnum ≤ Bstruct →
    (∀ i, Real.exp Rreq ≤ (N i : ℝ)) → Real.exp Rreq ≤ Rrank →
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) («I» := (PreparedSamplerContinuous (prep.pad (max m cutoff)))) («n» := (preparedSamplerTransverse (prep.pad (max m cutoff)))) («J» := (fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds (max m cutoff) (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff)))
          (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k) (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, PreparedScheduledDegreeModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k)
              (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := (max m cutoff)) (nX := nX) (M := M) (prep := (prep.pad (max m cutoff))) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood ∧
      ∃ (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
        (Acandidate : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S hb o hR (fun _ => hσ)
          N poly hmem τ (Real.exp (-Plate)) stride cells)
        (hξone : Real.exp (-Plate) ≤ 1),
      PreparedCenteredProductiveGoodCenterReadyConclusion (m := (max m cutoff)) (nX := nX) (M := M)
        (prep.pad (max m cutoff)) U b S bW hb o hR (fun _ => hσ) μ poly hmem stride
        (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S N τ (Real.exp (-Plate))) (Acandidate 0).bases
        gainLog gain Qgood (preparedSpatialKernelBlocks (max m cutoff) M nX) Acandidate.law N test
        (fun center =>
          letI : DecidableEq (Fin nX) := Classical.decEq _
          (∀ k : K, (Acandidate center).NativeDetection (degree k) (sliceLog k)
            (Pdetect.eval₂ (Nat.castRingHom ℝ) (pDetect k))
            (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants (max m cutoff) (degree k))
              (degree k + 1) (Pmaster k) Plate).nativeBudget (α k)) ∧
          letI : Nonempty (Acandidate center).Site := (Acandidate center).site_nonempty
          (FiniteProbabilityWeights.uniformFinset (integerBox N) (Acandidate center).integerBox_nonempty).excessMass
            ((Acandidate center).law.siteLaw ((Acandidate center).physicalBox hξone hmargin))
            (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j)) ≤
              6 * positiveProjectionAccuracy Econditional) := by
  intro A Cslice forecastCap Qw Pdetect K degree Cdetect kModel sourceU modelLog sliceLog u p
    pnum R pRadius D pDetect aDetect detectionGain Pk Pphysical target E Prho Ptail Pscale Tmod
    lengthLogs Pseed W Pmaster coarseTarget Plate τ α baseB0 Pwidth Bcert Pgood
    anchorRequired conditionalRequired detectorRequired Rreq hnum hNrequired hRankRequired
  obtain ⟨hA, _hextra, _hfront, hDensity, hSliceExponent, _hdegrees⟩ :=
    preparedFiniteNestedSourceExponent_bounds (max m cutoff) cutoff e Cprimitive Cdirect extra A
      (show preparedFiniteNestedSourceExponent (max m cutoff) cutoff e Cprimitive Cdirect extra ≤ A from le_rfl)
  have hQw : 0 ≤ Qw := by
    dsimp only [Qw]
    positivity
  have hWexp : W ≤ Real.exp Qw :=
    (preparedBadProductWitnessGap_bounds (max m cutoff) nX M hnum
      (show 0 ≤ gainLog + 8 by linarith only [hg]) hVlog Qgood hQgood hQexp).2
  have hCtail := prepared_commonRadius_densityCap_nested_bound (max m cutoff) A hDensity
    (prep.pad (max m cutoff)) le_rfl M
    (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))
    (prep.pad_coordinate_card_le hCoord) Bstruct hB hnum Vtail hVtail hprofile
    stageCountConstant innerDepth outerDepth innerDepth
  have hpnonneg : 0 ≤ p := preparedFiniteForwardWork_nonneg A stageCountConstant innerDepth
    (candidateNestedForwardSeed_nonneg A stageCountConstant innerDepth outerDepth hB)
  have hForecastCap : 0 ≤ forecastCap := by change (0 : ℝ) ≤ 1; norm_num
  have hForecastCapP : forecastCap ≤ Real.exp p := Real.one_le_exp_iff.mpr hpnonneg
  exact exists_preparedFiniteNestedForwardProductiveFixedCenterSource
    prep outerDepth innerDepth cutoff U b stride N Vtail Q hb o bW ν μ μrows
    A Cslice Cdirect stageCountConstant hA hSliceExponent
    Bstruct Qstride forecastCap stageLog Econditional Qσ Qw Pmin requestedCoarse gainLog gain Vlog
    Lmin Qgood hm hnX hCoord hB hstage hQstride hQσ hQw hPmin hLmin hg hVlog
    hQgood hQexp hgain hnChart hgChart hstride hstrideBound
    C hC hCbound hchart Cforward hforward hForward hVtail hVactual hprofile hcutoff
    cells hCells poly hp hmem Rrank hrank test htest hmean
    hnum hWexp hCtail hForecastCap hForecastCapP hNrequired hRankRequired

end Erdos3.VectorPolynomial

end

end OAI

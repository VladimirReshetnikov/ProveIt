/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Linear.KernelProjectionPresentPivotIdeal
import OAI.Combinatorics.Progressions.Sampling.ForecastResidualExponentialBudget
import OAI.Combinatorics.Progressions.Sampling.StagedForecastResidualBudget

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

structure CenteredForecastModel (X : Type*) where
  nterms : ℕ
  positive : 0 < nterms
  models : Fin nterms → X → ℂ
  coefficient : Fin nterms → ℝ
  residual : X → ℂ

variable {X Y F : Type*} [Fintype X] [MeasurableSpace Y]

def CenteredForecastModelBounds
    (jointLaw : Measure Y) (native : Set (X → ℂ))
    (reference : FiniteProbabilityWeights X) (forecast : F → X → ℂ)
    (localSeminorm : (X → ℂ) → ℝ)
    (selectedLocal : (X → ℂ) → (Y → ℂ) → Prop)
    (input : X → ℂ) (coefficientBound residualBound termBound : ℝ)
    (model : CenteredForecastModel X) : Prop :=
  (∀ i, model.models i ∈ native) ∧
  input = (∑ i, model.coefficient i • model.models i) + model.residual ∧
  (∑ i, |model.coefficient i|) ≤ coefficientBound ∧
  localSeminorm model.residual ≤ residualBound ∧
  (∀ f, ‖reference.correlation model.residual (forecast f)‖ ≤ residualBound) ∧
  (model.nterms : ℝ) ≤ termBound ∧
  ∀ errLocal : Y → ℂ, Measurable errLocal → selectedLocal model.residual errLocal →
    Integrable errLocal jointLaw ∧ (∫ y, ‖errLocal y‖ ∂jointLaw) ≤ residualBound

theorem exists_centeredFiniteForecastModels
    {Branch : Type*}
    (jointLaw : Measure Y) (native : Set (X → ℂ))
    (reference : FiniteProbabilityWeights X) (forecast : F → X → ℂ)
    (localSeminorm : (X → ℂ) → ℝ)
    (selectedLocal : (X → ℂ) → (Y → ℂ) → Prop)
    (input : Branch → X → ℂ) (inputBound coefficientBound residualBound termBound : ℝ)
    (hinput : ∀ b x, ‖input b x‖ ≤ inputBound)
    (hmodel : ∀ f : X → ℂ, (∀ x, ‖f x‖ ≤ inputBound) →
      ∃ model : CenteredForecastModel X,
        CenteredForecastModelBounds jointLaw native reference forecast localSeminorm
          selectedLocal f coefficientBound residualBound termBound model) :
    ∃ models : Branch → CenteredForecastModel X, ∀ b,
      CenteredForecastModelBounds jointLaw native reference forecast localSeminorm
        selectedLocal (input b) coefficientBound residualBound termBound (models b) := by
  classical
  exact Classical.skolem.mp (fun b => hmodel (input b) (hinput b))

theorem centeredFiniteForecastModels_integral_sum_norm_le
    {Branch : Type*} [Fintype Branch]
    (jointLaw : Measure Y) (native : Set (X → ℂ))
    (reference : FiniteProbabilityWeights X) (forecast : F → X → ℂ)
    (localSeminorm : (X → ℂ) → ℝ)
    (selectedLocal : (X → ℂ) → (Y → ℂ) → Prop)
    (input : Branch → X → ℂ) (coefficientBound residualBound termBound : ℝ)
    (models : Branch → CenteredForecastModel X)
    (hmodels : ∀ b, CenteredForecastModelBounds jointLaw native reference forecast
      localSeminorm selectedLocal (input b) coefficientBound residualBound termBound (models b))
    (errLocal : Branch → Y → ℂ) (hmeas : ∀ b, Measurable (errLocal b))
    (hselected : ∀ b, selectedLocal (models b).residual (errLocal b)) :
    (∀ b, Integrable (errLocal b) jointLaw) ∧
    Integrable (fun y => ∑ b, ‖errLocal b y‖) jointLaw ∧
    (∫ y, ∑ b, ‖errLocal b y‖ ∂jointLaw) ≤
      (Fintype.card Branch : ℝ) * residualBound := by
  have hlocal (b : Branch) := (hmodels b).2.2.2.2.2.2 (errLocal b) (hmeas b) (hselected b)
  refine ⟨fun b => (hlocal b).1,
    integrable_finsetSum _ (fun b _ => (hlocal b).1.norm), ?_⟩
  rw [integral_finsetSum _ (fun b _ => (hlocal b).1.norm)]
  calc
    _ ≤ ∑ _b : Branch, residualBound := Finset.sum_le_sum (fun b _ => (hlocal b).2)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

def centeredFiniteForecastResidualBadSet {Y Branch : Type*} [Fintype Branch]
    (errLocal : Branch → Y → ℂ) (δ : ℝ) : Set Y :=
  {y | δ < ∑ b, ‖errLocal b y‖}

theorem centeredFiniteForecastResidualBadSet_bound
    {Y Branch : Type*} [MeasurableSpace Y] [Fintype Branch]
    (jointLaw : Measure Y) [IsFiniteMeasure jointLaw]
    (errLocal : Branch → Y → ℂ) (hmeas : ∀ b, Measurable (errLocal b))
    (hint : Integrable (fun y => ∑ b, ‖errLocal b y‖) jointLaw)
    {residualBound δ : ℝ}
    (hintegral : (∫ y, ∑ b, ‖errLocal b y‖ ∂jointLaw) ≤
      (Fintype.card Branch : ℝ) * residualBound)
    (hδ : 0 < δ) :
    MeasurableSet (centeredFiniteForecastResidualBadSet errLocal δ) ∧
      jointLaw.real (centeredFiniteForecastResidualBadSet errLocal δ) ≤
        (Fintype.card Branch : ℝ) * residualBound / δ ∧
      ∀ y ∉ centeredFiniteForecastResidualBadSet errLocal δ, ∀ b, ‖errLocal b y‖ ≤ δ := by
  classical
  have hsum : Measurable (fun y => ∑ b, ‖errLocal b y‖) :=
    Finset.measurable_sum _ (fun b _ => (hmeas b).norm)
  have hnonneg : ∀ y, 0 ≤ ∑ b, ‖errLocal b y‖ :=
    fun y => Finset.sum_nonneg (fun b _ => norm_nonneg (errLocal b y))
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all jointLaw hnonneg) hint δ
  refine ⟨measurableSet_lt measurable_const hsum, ?_, ?_⟩
  · calc
      jointLaw.real (centeredFiniteForecastResidualBadSet errLocal δ) ≤
          jointLaw.real {y | δ ≤ ∑ b, ‖errLocal b y‖} :=
        measureReal_mono (fun y hy => show δ ≤ ∑ b, ‖errLocal b y‖ from le_of_lt hy)
      _ ≤ (∫ y, ∑ b, ‖errLocal b y‖ ∂jointLaw) / δ :=
        (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hmarkov)
      _ ≤ (Fintype.card Branch : ℝ) * residualBound / δ :=
        div_le_div_of_nonneg_right hintegral hδ.le
  · intro y hy b
    have hsumBound : (∑ b, ‖errLocal b y‖) ≤ δ := le_of_not_gt hy
    exact (Finset.single_le_sum (fun b _ => norm_nonneg (errLocal b y))
      (Finset.mem_univ b)).trans hsumBound

theorem centeredFiniteForecastModels_residualBadSet
    {X Y F Branch : Type*} [Fintype X] [MeasurableSpace Y] [Fintype Branch]
    (jointLaw : Measure Y) [IsFiniteMeasure jointLaw]
    (native : Set (X → ℂ)) (reference : FiniteProbabilityWeights X)
    (forecast : F → X → ℂ) (localSeminorm : (X → ℂ) → ℝ)
    (selectedLocal : (X → ℂ) → (Y → ℂ) → Prop)
    (input : Branch → X → ℂ) (coefficientBound termBound : ℝ)
    (models : Branch → CenteredForecastModel X)
    {u E Bbranch gainLog gain : ℝ}
    (hmodels : ∀ b, CenteredForecastModelBounds jointLaw native reference forecast
      localSeminorm selectedLocal (input b) coefficientBound (Real.exp (-u)) termBound (models b))
    (errLocal : Branch → Y → ℂ) (hmeas : ∀ b, Measurable (errLocal b))
    (hselected : ∀ b, selectedLocal (models b).residual (errLocal b))
    (hbranch : (Fintype.card Branch : ℝ) ≤ Real.exp Bbranch)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hu : Bbranch + gainLog + E + 6 ≤ u) :
    MeasurableSet (centeredFiniteForecastResidualBadSet errLocal (Real.exp (-E))) ∧
      jointLaw.real (centeredFiniteForecastResidualBadSet errLocal (Real.exp (-E))) ≤ gain / 32 ∧
      ∀ y ∉ centeredFiniteForecastResidualBadSet errLocal (Real.exp (-E)),
        ∀ b, ‖errLocal b y‖ ≤ Real.exp (-E) := by
  obtain ⟨_, hint, hintegral⟩ := centeredFiniteForecastModels_integral_sum_norm_le
    jointLaw native reference forecast localSeminorm selectedLocal input coefficientBound
    (Real.exp (-u)) termBound models hmodels errLocal hmeas hselected
  obtain ⟨hbadMeas, hbadMass, hbranchBound⟩ :=
    centeredFiniteForecastResidualBadSet_bound jointLaw errLocal hmeas hint hintegral
      (Real.exp_pos (-E))
  exact ⟨hbadMeas, hbadMass.trans (forecastResidualExponentialBudget hbranch hgain hu),
    hbranchBound⟩

theorem centeredFiniteForecastModels_centeredResidualBadSet
    {X C Ω F Branch : Type*} [Fintype X] [MeasurableSpace C]
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Branch]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (native : Set (X → ℂ)) (reference : FiniteProbabilityWeights X)
    (forecast : F → X → ℂ) (localSeminorm : (X → ℂ) → ℝ)
    (selectedLocal : (X → ℂ) → (C × Ω → ℂ) → Prop)
    (input : Branch → X → ℂ) (coefficientBound termBound : ℝ)
    (models : Branch → CenteredForecastModel X)
    {u E Bbranch gainLog gain : ℝ}
    (hmodels : ∀ b, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
      native reference forecast localSeminorm selectedLocal (input b)
      coefficientBound (Real.exp (-u)) termBound (models b))
    (errLocal : Branch → C × Ω → ℂ) (hmeas : ∀ b, Measurable (errLocal b))
    (hselected : ∀ b, selectedLocal (models b).residual (errLocal b))
    (hbranch : (Fintype.card Branch : ℝ) ≤ Real.exp Bbranch)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hu : Bbranch + gainLog + E + 6 ≤ u) :
    MeasurableSet (centeredFiniteForecastResidualBadSet errLocal (Real.exp (-E))) ∧
      (centeredFiniteProbabilityMeasure μ law).real
        (centeredFiniteForecastResidualBadSet errLocal (Real.exp (-E))) ≤ gain / 32 ∧
      ∀ y ∉ centeredFiniteForecastResidualBadSet errLocal (Real.exp (-E)),
        ∀ b, ‖errLocal b y‖ ≤ Real.exp (-E) := by
  let := centeredFiniteProbabilityMeasure_probability μ law hweight
  exact centeredFiniteForecastModels_residualBadSet (centeredFiniteProbabilityMeasure μ law)
    native reference forecast localSeminorm selectedLocal input coefficientBound termBound
    models hmodels errLocal hmeas hselected hbranch hgain hu

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

def centeredFiniteForecastUniformResidualBadSet
    {C Ω T X Branch : Type*} [Fintype T] [Fintype Branch] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) (signal : Branch → X → ℂ) (δ : ℝ) : Set (C × Ω) :=
  {y | δ < ∑ b, centeredFiniteSliceResidualEnvelope physical slices tests (signal b) y.2}

theorem centeredFiniteForecastUniformResidualBadSet_bound
    {C Ω T X Branch : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype T] [Nonempty T] [Fintype Branch] {J : Ω → Type*}
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun c => (law c).weight z))
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) {K : ℝ}
    (hslices : ∀ z j, (slices z j).Nonempty)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (signal : Branch → X → ℂ) {residualBound δ : ℝ}
    (hlocal : ∀ b, sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
      physical slices tests (signal b) ≤ residualBound)
    (hδ : 0 < δ) :
    MeasurableSet (centeredFiniteForecastUniformResidualBadSet (C := C) physical slices tests signal δ) ∧
      (centeredFiniteProbabilityMeasure μ law).real
        (centeredFiniteForecastUniformResidualBadSet (C := C) physical slices tests signal δ) ≤
          (Fintype.card Branch : ℝ) * residualBound / δ ∧
      ∀ y ∉ centeredFiniteForecastUniformResidualBadSet (C := C) physical slices tests signal δ,
        ∀ b j, ‖𝔼 t ∈ slices y.2 j, signal b (physical y.2 t) * tests y.2 j t‖ ≤ δ := by
  classical
  let := centeredFiniteProbabilityMeasure_probability μ law hweight
  have henv (b : Branch) := centeredFiniteSliceResidualEnvelope_joint
    μ law hweight physical slices tests (signal b)
  have hsumMeas : Measurable (fun y : C × Ω =>
      ∑ b, centeredFiniteSliceResidualEnvelope physical slices tests (signal b) y.2) :=
    Finset.measurable_sum _ (fun b _ => (henv b).1)
  have hsumInt : Integrable (fun y : C × Ω =>
      ∑ b, centeredFiniteSliceResidualEnvelope physical slices tests (signal b) y.2)
      (centeredFiniteProbabilityMeasure μ law) :=
    integrable_finsetSum _ (fun b _ => (henv b).2.1)
  have hsumBound : (∫ y, ∑ b,
      centeredFiniteSliceResidualEnvelope physical slices tests (signal b) y.2
      ∂centeredFiniteProbabilityMeasure μ law) ≤ (Fintype.card Branch : ℝ) * residualBound := by
    rw [integral_finsetSum _ (fun b _ => (henv b).2.1)]
    calc
      _ ≤ ∑ _b : Branch, residualBound := Finset.sum_le_sum (fun b _ => by
        rw [(henv b).2.2]
        exact hlocal b)
      _ = _ := by simp
  have hnonneg (y : C × Ω) :
      0 ≤ ∑ b, centeredFiniteSliceResidualEnvelope physical slices tests (signal b) y.2 :=
    Finset.sum_nonneg (fun b _ =>
      centeredFiniteSliceResidualEnvelope_nonneg physical slices tests (signal b) y.2)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (centeredFiniteProbabilityMeasure μ law) hnonneg) hsumInt δ
  refine ⟨measurableSet_lt measurable_const hsumMeas, ?_, ?_⟩
  · calc
      _ ≤ (centeredFiniteProbabilityMeasure μ law).real
          {y | δ ≤ ∑ b, centeredFiniteSliceResidualEnvelope physical slices tests (signal b) y.2} :=
        measureReal_mono (fun y hy => show δ ≤ ∑ b,
          centeredFiniteSliceResidualEnvelope physical slices tests (signal b) y.2 from le_of_lt hy)
      _ ≤ (∫ y, ∑ b, centeredFiniteSliceResidualEnvelope physical slices tests (signal b) y.2
          ∂centeredFiniteProbabilityMeasure μ law) / δ :=
        (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hmarkov)
      _ ≤ (Fintype.card Branch : ℝ) * residualBound / δ :=
        div_le_div_of_nonneg_right hsumBound hδ.le
  · intro y hy b j
    have hsumSmall : (∑ b,
        centeredFiniteSliceResidualEnvelope physical slices tests (signal b) y.2) ≤ δ :=
      le_of_not_gt hy
    have hbranch := (Finset.single_le_sum
      (fun b _ => centeredFiniteSliceResidualEnvelope_nonneg physical slices tests (signal b) y.2)
      (Finset.mem_univ b)).trans hsumSmall
    exact (centeredFiniteSliceResidualEnvelope_dominates physical slices tests
      hslices hsize htests (signal b) y.2 j).trans hbranch

theorem centeredFiniteForecastModels_uniformResidualBadSet
    {X C Ω T F Branch : Type*} [Fintype X] [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype T] [Nonempty T]
    [Fintype Branch] {J : Ω → Type*}
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) {K : ℝ}
    (hslices : ∀ z j, (slices z j).Nonempty)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (native : Set (X → ℂ)) (reference : FiniteProbabilityWeights X)
    (forecast : F → X → ℂ) (selectedLocal : (X → ℂ) → (C × Ω → ℂ) → Prop)
    (input : Branch → X → ℂ) (coefficientBound termBound : ℝ)
    (models : Branch → CenteredForecastModel X)
    {u E Bbranch gainLog gain : ℝ}
    (hmodels : ∀ b, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
      native reference forecast
      (sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical slices tests)
      selectedLocal (input b) coefficientBound (Real.exp (-u)) termBound (models b))
    (hbranch : (Fintype.card Branch : ℝ) ≤ Real.exp Bbranch)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hu : Bbranch + gainLog + E + 6 ≤ u) :
    MeasurableSet (centeredFiniteForecastUniformResidualBadSet (C := C) physical slices tests
      (fun b => (models b).residual) (Real.exp (-E))) ∧
      (centeredFiniteProbabilityMeasure μ law).real
        (centeredFiniteForecastUniformResidualBadSet (C := C) physical slices tests
          (fun b => (models b).residual) (Real.exp (-E))) ≤ gain / 32 ∧
      ∀ y ∉ centeredFiniteForecastUniformResidualBadSet (C := C) physical slices tests
          (fun b => (models b).residual) (Real.exp (-E)), ∀ b j,
        ‖𝔼 t ∈ slices y.2 j, (models b).residual (physical y.2 t) * tests y.2 j t‖ ≤
          Real.exp (-E) := by
  obtain ⟨hmeas, hmass, hlocal⟩ := centeredFiniteForecastUniformResidualBadSet_bound
    μ law hweight physical slices tests hslices hsize htests (fun b => (models b).residual)
    (fun b => (hmodels b).2.2.2.1) (Real.exp_pos (-E))
  exact ⟨hmeas, hmass.trans (forecastResidualExponentialBudget hbranch hgain hu), hlocal⟩

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

def centeredStagedForecastUniformResidualBadSet
    {C Ω T X Stage : Type*} [Fintype T]
    {Branch : Stage → Type*} [∀ k, Fintype (Branch k)]
    {Tests : Stage → Ω → Type*}
    (physical : Ω → T → X)
    (slices : ∀ k z, Tests k z → Finset T)
    (tests : ∀ k z, Tests k z → T → ℂ)
    (signal : ∀ k, Branch k → X → ℂ) (Eres : Stage → ℝ) : Set (C × Ω) :=
  ⋃ k, centeredFiniteForecastUniformResidualBadSet (C := C)
    physical (slices k) (tests k) (signal k) (Real.exp (-Eres k))

theorem centeredStagedForecastUniformResidualBadSet_bound
    {C Ω T X Stage : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype T] [Nonempty T] [Fintype Stage]
    {Branch : Stage → Type*} [∀ k, Fintype (Branch k)]
    {Tests : Stage → Ω → Type*}
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun c => (law c).weight z))
    (physical : Ω → T → X)
    (slices : ∀ k z, Tests k z → Finset T)
    (tests : ∀ k z, Tests k z → T → ℂ) {K : Stage → ℝ}
    (hslices : ∀ k z j, (slices k z j).Nonempty)
    (hsize : ∀ k z j, (Fintype.card T : ℝ) / (slices k z j).card ≤ K k)
    (htests : ∀ k z j t, ‖tests k z j t‖ ≤ 1)
    (signal : ∀ k, Branch k → X → ℂ)
    (u B Eres : Stage → ℝ) {gainLog gain stageLog : ℝ}
    (hlocal : ∀ k b, sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
      physical (slices k) (tests k) (signal k b) ≤ Real.exp (-u k))
    (hbranch : ∀ k, (Fintype.card (Branch k) : ℝ) ≤ Real.exp (B k))
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hstage : (Fintype.card Stage : ℝ) + 1 ≤ Real.exp stageLog)
    (hu : ∀ k, B k + gainLog + Eres k + stageLog + 6 ≤ u k) :
    MeasurableSet (centeredStagedForecastUniformResidualBadSet (C := C)
      physical slices tests signal Eres) ∧
      (centeredFiniteProbabilityMeasure μ law).real
        (centeredStagedForecastUniformResidualBadSet (C := C) physical slices tests signal Eres) ≤
          gain / 32 ∧
      ∀ y ∉ centeredStagedForecastUniformResidualBadSet (C := C)
          physical slices tests signal Eres, ∀ k b j,
        ‖𝔼 t ∈ slices k y.2 j, signal k b (physical y.2 t) * tests k y.2 j t‖ ≤
          Real.exp (-Eres k) := by
  classical
  let := centeredFiniteProbabilityMeasure_probability μ law hweight
  let stageBad := fun k => centeredFiniteForecastUniformResidualBadSet (C := C)
    physical (slices k) (tests k) (signal k) (Real.exp (-Eres k))
  have hsplitGain := stagedForecastResidual_gain_lower hstage hgain
  have hstageBounds (k : Stage) : MeasurableSet (stageBad k) ∧
      (centeredFiniteProbabilityMeasure μ law).real (stageBad k) ≤
        (gain / ((Fintype.card Stage : ℝ) + 1)) / 32 ∧
      ∀ y ∉ stageBad k, ∀ b j,
        ‖𝔼 t ∈ slices k y.2 j, signal k b (physical y.2 t) * tests k y.2 j t‖ ≤
          Real.exp (-Eres k) := by
    obtain ⟨hmeas, hmass, hpoint⟩ := centeredFiniteForecastUniformResidualBadSet_bound
      μ law hweight physical (slices k) (tests k) (hslices k) (hsize k) (htests k)
      (signal k) (hlocal k) (Real.exp_pos (-Eres k))
    refine ⟨hmeas, hmass.trans ?_, hpoint⟩
    exact forecastResidualExponentialBudget (hbranch k) hsplitGain
      (by linarith only [hu k])
  refine ⟨MeasurableSet.iUnion (fun k => (hstageBounds k).1), ?_, ?_⟩
  · calc
      _ ≤ ∑ k, (centeredFiniteProbabilityMeasure μ law).real (stageBad k) :=
        measureReal_iUnion_fintype_le stageBad
      _ ≤ ∑ _k : Stage, (gain / ((Fintype.card Stage : ℝ) + 1)) / 32 :=
        Finset.sum_le_sum (fun k _ => (hstageBounds k).2.1)
      _ ≤ gain / 32 := stagedForecastResidual_sum_bound
        ((Real.exp_nonneg (-gainLog)).trans hgain)
  · intro y hy k b j
    have hyStage : y ∉ stageBad k := fun hk => hy (Set.mem_iUnion.mpr ⟨k, hk⟩)
    exact (hstageBounds k).2.2 y hyStage b j

theorem centeredStagedForecastModels_uniformResidualBadSet
    {C Ω T X Stage : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype T] [Nonempty T] [Fintype Stage]
    {Branch : Stage → Type*} [∀ k, Fintype (Branch k)]
    {Tests : Stage → Ω → Type*}
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun c => (law c).weight z))
    (physical : Ω → T → X)
    (slices : ∀ k z, Tests k z → Finset T)
    (tests : ∀ k z, Tests k z → T → ℂ) {K : Stage → ℝ}
    (hslices : ∀ k z j, (slices k z j).Nonempty)
    (hsize : ∀ k z j, (Fintype.card T : ℝ) / (slices k z j).card ≤ K k)
    (htests : ∀ k z j t, ‖tests k z j t‖ ≤ 1)
    (models : ∀ k, Branch k → CenteredForecastModel X)
    (u B Eres : Stage → ℝ) {gainLog gain stageLog : ℝ}
    (hlocal : ∀ k b, sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
      physical (slices k) (tests k) (models k b).residual ≤ Real.exp (-u k))
    (hbranch : ∀ k, (Fintype.card (Branch k) : ℝ) ≤ Real.exp (B k))
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hstage : (Fintype.card Stage : ℝ) + 1 ≤ Real.exp stageLog)
    (hu : ∀ k, B k + gainLog + Eres k + stageLog + 6 ≤ u k) :
    MeasurableSet (centeredStagedForecastUniformResidualBadSet (C := C)
      physical slices tests (fun k b => (models k b).residual) Eres) ∧
      (centeredFiniteProbabilityMeasure μ law).real
        (centeredStagedForecastUniformResidualBadSet (C := C)
          physical slices tests (fun k b => (models k b).residual) Eres) ≤ gain / 32 ∧
      ∀ y ∉ centeredStagedForecastUniformResidualBadSet (C := C)
          physical slices tests (fun k b => (models k b).residual) Eres, ∀ k b j,
        ‖𝔼 t ∈ slices k y.2 j, (models k b).residual (physical y.2 t) * tests k y.2 j t‖ ≤
          Real.exp (-Eres k) :=
  centeredStagedForecastUniformResidualBadSet_bound μ law hweight physical slices tests
    hslices hsize htests (fun k b => (models k b).residual) u B Eres
    hlocal hbranch hgain hstage hu

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_fixed_linear_model_partners_of_pointwise_error
    {Ω K V : Type*} {I : K → Type*}
    [Fintype Ω] [Fintype K] [∀ k, Fintype (I k)] [∀ k, Nonempty (I k)]
    [AddCommGroup V] [Module ℂ V]
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (v e : K → V) (Q : ∀ k, I k → V) (c : ∀ k, I k → ℂ)
    (test : Ω → K → V →ₗ[ℂ] ℂ)
    (hmodel : ∀ k, v k = (∑ i, c k i • Q k i) + e k)
    {delta M : ℝ} (hdelta : 0 < delta) (hM : 0 < M)
    (hc : ∀ k, (∑ i, ‖c k i‖) ≤ M)
    (herr : ∀ a ∈ productive, ∀ k, ‖test a k (e k)‖ ≤ delta / 2)
    (hscore : ∀ a ∈ productive, ∀ k, delta ≤ ‖test a k (v k)‖) :
    ∃ (partner : ∀ k, I k) (retained : Finset Ω),
      retained ⊆ productive ∧
      outer.mass productive / (∏ k, (Fintype.card (I k) : ℝ)) ≤ outer.mass retained ∧
      ∀ a ∈ retained, ∀ k, delta / (2 * M) ≤ ‖test a k (Q k (partner k))‖ := by
  have hex (a : Ω) (ha : a ∈ productive) (k : K) :
      ∃ i, delta / (2 * M) ≤ ‖test a k (Q k i)‖ :=
    exists_linear_model_partner (test a k) (v k) (e k) (Q k) (c k) (hmodel k)
      hdelta hM (hc k) (herr a ha k) (hscore a ha k)
  let choice : Ω → ∀ k, I k := fun a k =>
    if ha : a ∈ productive then Classical.choose (hex a ha k)
    else Classical.choice inferInstance
  have hchoice (a : Ω) (ha : a ∈ productive) (k : K) :
      delta / (2 * M) ≤ ‖test a k (Q k (choice a k))‖ := by
    dsimp only [choice]
    rw [dite_eq_left ha]
    exact Classical.choose_spec (hex a ha k)
  obtain ⟨partner, hmass⟩ := outer.exists_code_fiber_mass productive choice
  refine ⟨partner, productive.filter (fun a => choice a = partner),
    Finset.filter_subset _ _, ?_, ?_⟩
  · rw [Fintype.card_pi, Nat.cast_prod] at hmass
    convert hmass using 1
    congr 1
    ext a
    simp only [Finset.mem_filter]
  · intro a ha k
    obtain ⟨hap, heq⟩ := Finset.mem_filter.mp ha
    rw [← heq]
    exact hchoice a hap k

theorem exists_precenter_forecast_native_partners
    {Ω T X Branch K σ Θ : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype K]
    (input : Branch → X → ℂ) (models : Branch → CenteredForecastModel X)
    (nativeWeight : σ → ℕ) (degree : ℕ) (budget : ℝ)
    (sample : X → σ → ℤ) (twist : Θ → X → ℂ)
    (hnative : ∀ b i, (models b).models i ∈
      twistedNativeSampleFunctions nativeWeight degree budget sample twist)
    (hmodel : ∀ b, input b =
      (∑ i, (models b).coefficient i • (models b).models i) + (models b).residual)
    {M termBound delta : ℝ} {rank : ℕ}
    (hM : 0 < M) (hterm : 1 ≤ termBound) (hdelta : 0 < delta)
    (hc : ∀ b, (∑ i, |(models b).coefficient i|) ≤ M)
    (hterms : ∀ b, ((models b).nterms : ℝ) ≤ termBound)
    (selectedBranch : K → Branch) (hrank : Fintype.card K ≤ rank)
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (hproductive : 0 < outer.mass productive)
    (physical : Ω → T → X) (slices : Ω → K → Finset T)
    (weight : Ω → K → T → ℂ) (hS : ∀ a k, (slices a k).Nonempty)
    (herr : ∀ a ∈ productive, ∀ k,
      ‖𝔼 t ∈ slices a k, (models (selectedBranch k)).residual (physical a t) *
        weight a k t‖ ≤ delta / 2)
    (hscore : ∀ a ∈ productive, ∀ k, delta ≤
      ‖𝔼 t ∈ slices a k, input (selectedBranch k) (physical a t) * weight a k t‖) :
    ∃ (fixedTwist : K → Θ) (nativeValue : K → X → ℂ)
      (_native : ∀ k, NativeSampleModel nativeWeight degree budget sample (nativeValue k))
      (retained : Finset Ω),
      retained ⊆ productive ∧ 0 < outer.mass retained ∧
      outer.mass productive / termBound ^ rank ≤ outer.mass retained ∧
      ∀ a ∈ retained, ∀ k, delta / (2 * M) ≤
        ‖𝔼 t ∈ slices a k,
          (star (twist (fixedTwist k) (physical a t)) * nativeValue k (physical a t)) *
            weight a k t‖ := by
  let selectedModel := fun k => models (selectedBranch k)
  let : ∀ k, Nonempty (Fin (selectedModel k).nterms) :=
    fun k => ⟨⟨0, (selectedModel k).positive⟩⟩
  let test := fun a k => sampledTestLinearMap (physical a)
    (normalizedSliceTest (slices a k) (weight a k))
  have heval (a) (k) (f : X → ℂ) : test a k f =
      𝔼 t ∈ slices a k, f (physical a t) * weight a k t :=
    normalizedSliceTest_mean _ (hS a k) _ _
  have hmodelComplex (k : K) : input (selectedBranch k) =
      (∑ i, ((selectedModel k).coefficient i : ℂ) • (selectedModel k).models i) +
        (selectedModel k).residual := hmodel (selectedBranch k)
  have hcComplex (k : K) : ∑ i, ‖((selectedModel k).coefficient i : ℂ)‖ ≤ M := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hc (selectedBranch k)
  obtain ⟨partner, retained, hsub, hmass, hcorr⟩ :=
    exists_fixed_linear_model_partners_of_pointwise_error outer productive
      (fun k => input (selectedBranch k)) (fun k => (selectedModel k).residual)
      (fun k => (selectedModel k).models)
      (fun k i => ((selectedModel k).coefficient i : ℂ)) test
      hmodelComplex hdelta hM hcComplex
      (by intro a ha k; rw [heval]; exact herr a ha k)
      (by intro a ha k; rw [heval]; exact hscore a ha k)
  have hmasspos : 0 < outer.mass retained :=
    (div_pos hproductive (Finset.prod_pos (fun k _ =>
      Nat.cast_pos.mpr Fintype.card_pos))).trans_le hmass
  have hne : retained.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmasspos
    linarith)
  obtain ⟨a₀, ha₀⟩ := hne
  have hchosen (k : K) : ∃ (t : Θ) (g : X → ℂ),
      Nonempty (NativeSampleModel nativeWeight degree budget sample g) ∧
      (selectedModel k).models (partner k) = fun x => star (twist t x) * g x := by
    rcases hnative (selectedBranch k) (partner k) with hzero | hgood
    · have hn := hcorr a₀ ha₀ k
      change delta / (2 * M) ≤ ‖test a₀ k ((models (selectedBranch k)).models (partner k))‖ at hn
      rw [hzero, map_zero, norm_zero] at hn
      have hpos : 0 < delta / (2 * M) := div_pos hdelta (by positivity)
      linarith
    · exact hgood
  choose fixedTwist nativeValue hnativeValue heq using hchosen
  refine ⟨fixedTwist, nativeValue, fun k => Classical.choice (hnativeValue k),
    retained, hsub, hmasspos, ?_, ?_⟩
  · apply le_trans _ hmass
    apply div_le_div_of_nonneg_left hproductive.le
      (Finset.prod_pos (fun k _ => Nat.cast_pos.mpr Fintype.card_pos))
    calc
      (∏ k, (Fintype.card (Fin (selectedModel k).nterms) : ℝ))
          ≤ ∏ _k : K, termBound := by
        apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        intro k _
        simpa only [Fintype.card_fin] using hterms (selectedBranch k)
      _ = termBound ^ Fintype.card K := by rw [Finset.prod_const, Finset.card_univ]
      _ ≤ termBound ^ rank := pow_le_pow_right₀ hterm hrank
  · intro a ha k
    have h := hcorr a ha k
    rw [heval, heq] at h
    exact h

end Erdos3

end

end OAI

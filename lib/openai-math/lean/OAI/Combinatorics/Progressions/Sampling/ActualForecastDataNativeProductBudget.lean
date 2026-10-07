import OAI.Combinatorics.Progressions.Dynamics.NormalizedTwistProductBudget
import OAI.Combinatorics.Progressions.Estimates.NormalizedNativeFamilyMonotone
import OAI.Combinatorics.Progressions.Estimates.NormalizedTwistNativeMembership
import OAI.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

theorem forecastNormalizedTwist_mem_fixed_native_family
    {X Ω : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0} {budget : ℝ}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (hperiod : periodCap ≤ Real.exp budget) (hcover : coverCap ≤ Real.exp budget)
    (hL : (L : ℝ) ≤ Real.exp budget) (hbudget : 2 ≤ budget)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (degree : ℕ) :
    (fun t => W.eval N poly (sample t)) ∈ twistedNativeSampleFunctions w degree budget sample
      (fun (V : NormalizedPolynomialTwist X (Σ j, J j) (Real.exp budget) (Real.exp budget)
        ⟨Real.exp budget, Real.exp_nonneg _⟩) t => V.eval N poly (sample t)) := by
  let V := W.mono hperiod hcover (show L ≤ ⟨Real.exp budget, Real.exp_nonneg _⟩ from hL)
  have h := normalizedTwist_eval_mem_twistedNativeSampleFunctions V N poly sample w degree hbudget
  have he : (fun t => V.eval N poly (sample t)) = (fun t => W.eval N poly (sample t)) := rfl
  rw [he] at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

theorem forecastBufferedTwist_lipschitz_exp_bound {P : ℝ} (hP : 0 ≤ P)
    (q : ℕ) (L Lcoord Lcut : ℝ≥0)
    (hq : (q : ℝ) ≤ Real.exp P) (hL : (L : ℝ) ≤ Real.exp P)
    (hcoord : (Lcoord : ℝ) ≤ Real.exp P) (hcut : (Lcut : ℝ) ≤ Real.exp P) :
    ((Lcut * q + max ((L * max 1 Lcoord) * max 1 (q : ℝ≥0)) (4 * q) : ℝ≥0) : ℝ) ≤
      Real.exp (3 * P + 3) := by
  have hone : (1 : ℝ) ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have he2 : Real.exp P * Real.exp P = Real.exp (2 * P) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he3 : Real.exp (2 * P) * Real.exp P = Real.exp (3 * P) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod : (L : ℝ) * max 1 (Lcoord : ℝ) * max 1 (q : ℝ) ≤ Real.exp (3 * P) := by
    calc
      _ ≤ (Real.exp P * Real.exp P) * Real.exp P :=
        mul_le_mul (mul_le_mul hL (max_le hone hcoord) (by positivity) (Real.exp_pos _).le)
          (max_le hone hq) (by positivity) (by positivity)
      _ = _ := by rw [he2, he3]
  have hfirst : (Lcut : ℝ) * q ≤ Real.exp (2 * P) := by
    exact (mul_le_mul hcut hq (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq he2
  have he23 : Real.exp (2 * P) ≤ Real.exp (3 * P) := Real.exp_le_exp.mpr (by linarith)
  have he13 : Real.exp P ≤ Real.exp (3 * P) := Real.exp_le_exp.mpr (by linarith)
  have hfour : (4 : ℝ) * q ≤ 4 * Real.exp (3 * P) :=
    mul_le_mul_of_nonneg_left (hq.trans he13) (by norm_num)
  have hmax : max ((L : ℝ) * max 1 (Lcoord : ℝ) * max 1 (q : ℝ)) (4 * q) ≤
      4 * Real.exp (3 * P) := max_le (hprod.trans (by nlinarith [Real.exp_pos (3 * P)])) hfour
  have hfive : (5 : ℝ) ≤ Real.exp 3 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)
    norm_num at h ⊢
    linarith
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_max, NNReal.coe_one,
    NNReal.coe_ofNat]
  calc
    _ ≤ 5 * Real.exp (3 * P) := by linarith [hfirst.trans he23]
    _ ≤ Real.exp 3 * Real.exp (3 * P) :=
      mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem forecastBufferedTwist_mem_early_native_family
    {X Ω : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (hP : 0 ≤ P) (q : ℕ) (L Lcoord Lcut : ℝ≥0)
    (hq : (q : ℝ) ≤ Real.exp P) (hL : (L : ℝ) ≤ Real.exp P)
    (hcoord : (Lcoord : ℝ) ≤ Real.exp P) (hcut : (Lcut : ℝ) ≤ Real.exp P)
    (W : NormalizedPolynomialTwist X (Σ j, J j) q q
      (Lcut * q + max ((L * max 1 Lcoord) * max 1 (q : ℝ≥0)) (4 * q)))
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (degree : ℕ) :
    (fun t => W.eval N poly (sample t)) ∈ twistedNativeSampleFunctions w degree (3 * P + 3) sample
      (fun (V : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * P + 3)) (Real.exp (3 * P + 3))
        ⟨Real.exp (3 * P + 3), Real.exp_nonneg _⟩) t => V.eval N poly (sample t)) := by
  have hq' : (q : ℝ) ≤ Real.exp (3 * P + 3) :=
    hq.trans (Real.exp_le_exp.mpr (by linarith))
  exact forecastNormalizedTwist_mem_fixed_native_family W hq' hq'
    (forecastBufferedTwist_lipschitz_exp_bound hP q L Lcoord Lcut hq hL hcoord hcut)
    (by linarith) N poly sample w degree

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

theorem forecastFiniteTwists_common_family
    {X Ω Term : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (localBudget Pnative : ℝ) (hPn : 0 ≤ Pnative)
    (twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
      (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
      ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (degree : ℕ) :
    let budget := max localBudget (3 * Pnative + 3)
    (∀ t, (fun ω => (twists t).eval N poly (sample ω)) ∈
      twistedNativeSampleFunctions w degree budget sample
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩) ω =>
            W.eval N poly (sample ω))) ∧
    (twistedNativeSampleFunctions w degree localBudget sample
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp localBudget) (Real.exp localBudget)
          ⟨Real.exp localBudget, Real.exp_nonneg _⟩) ω => W.eval N poly (sample ω)) ⊆
      twistedNativeSampleFunctions w degree budget sample
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩) ω =>
            W.eval N poly (sample ω))) := by
  intro budget
  have hle : 3 * Pnative + 3 ≤ budget := le_max_right _ _
  have hbudget : 2 ≤ budget := (show 2 ≤ 3 * Pnative + 3 by linarith).trans hle
  refine ⟨?_, normalizedNativeSampleFunctions_mono N poly w degree sample (le_max_left _ _)⟩
  intro t
  exact forecastNormalizedTwist_mem_fixed_native_family (twists t)
    (Real.exp_le_exp.mpr hle) (Real.exp_le_exp.mpr hle) (Real.exp_le_exp.mpr hle)
    hbudget N poly sample w degree

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {X Ω Forecast : Type*} [Fintype X]
variable {Term : Forecast → Type*} {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem centeredForecastTwist_mem_common_family
    {sample : Ω → X → ℤ} {w : X → ℕ} {degree : ℕ}
    (localBudget Pnative : ℝ) (hPn : 0 ≤ Pnative)
    (twists : ∀ f, Term f → NormalizedPolynomialTwist X (Σ j, J j)
      (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
      ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Forecast → ∀ j, J j → ℝ) (f : Forecast) (i : Term f) :
    let budget := max localBudget (3 * Pnative + 3)
    (fun ω => ((twists f i).shiftConstant (c f)).eval N poly (sample ω)) ∈
      twistedNativeSampleFunctions w degree budget sample
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩) ω =>
            W.eval N poly (sample ω)) := by
  exact (forecastFiniteTwists_common_family localBudget Pnative hPn
    (fun i => (twists f i).shiftConstant (c f)) N poly sample w degree).1 i

theorem centeredForecastTwist_eval_mem_common_family
    {sample : Ω → X → ℤ} {w : X → ℕ} {degree : ℕ}
    (localBudget Pnative : ℝ) (hPn : 0 ≤ Pnative)
    (twists : ∀ f, Term f → NormalizedPolynomialTwist X (Σ j, J j)
      (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
      ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Forecast → ∀ j, J j → ℝ) (f : Forecast) (i : Term f) :
    let budget := max localBudget (3 * Pnative + 3)
    (fun ω => (twists f i).eval N (fun j => subtractConstant (c f j) (poly j)) (sample ω)) ∈
      twistedNativeSampleFunctions w degree budget sample
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩) ω =>
            W.eval N poly (sample ω)) := by
  intro budget
  have he :
      (fun ω => ((twists f i).shiftConstant (c f)).eval N poly (sample ω)) =
      (fun ω => (twists f i).eval N (fun j => subtractConstant (c f j) (poly j)) (sample ω)) := by
    funext ω
    exact (twists f i).eval_shiftConstant (c f) N poly (sample ω)
  rw [← he]
  exact centeredForecastTwist_mem_common_family localBudget Pnative hPn twists N poly c f i

theorem centeredForecastTwist_sum_eq
    [∀ f, Fintype (Term f)] {periodCap coverCap : ℝ} {L : ℝ≥0}
    (twists : ∀ f, Term f → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (coeff : ∀ f, Term f → ℂ)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Forecast → ∀ j, J j → ℝ) (f : Forecast) (u : X → ℤ) :
    (∑ i, coeff f i * ((twists f i).shiftConstant (c f)).eval N poly u) =
      ∑ i, coeff f i * (twists f i).eval N (fun j => subtractConstant (c f j) (poly j)) u := by
  simp only [NormalizedPolynomialTwist.eval_shiftConstant]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_centered_forecast_twist_model
    {Center Ω T X Forecast : Type*} [MeasurableSpace Center] [Nonempty Forecast] [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (localBudget Pnative : ℝ) (hlocalBudget : 0 ≤ localBudget) (hPnative : 0 ≤ Pnative)
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : Measure Center) [IsProbabilityMeasure μ]
    (law : Center → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (forecast : Forecast → integerBox N → ℂ)
    {u p P massLog K C forecastCap εtail : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hmassLog : 0 ≤ massLog)
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hforecastCapP : forecastCap ≤ Real.exp p)
    (hP : u + 2 * p +
      max (max localBudget (3 * Pnative + 3)) (2 * u + 4 * p + massLog + 20) + 32 ≤ P)
    (hslices : ∀ z j, (slices z j).Nonempty)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f u, ‖forecast f u‖ ≤ forecastCap)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ u, ‖signal u‖ ≤ 1) →
      (∀ u, u ∉ integerBox N → signal u = 0) →
      forecastAugmentedUnitThreshold u p K C forecastCap ≤
        sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp localBudget) (Real.exp localBudget)
          ⟨Real.exp localBudget, Real.exp_nonneg _⟩)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel (1 : X → ℕ) 0 localBudget
          (fun u : integerBox N => u.val) G) ∧
        Real.exp (-localBudget) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun u => signal u.val)
          (fun u => star (W.eval N poly u.val) * G u)‖)
    (Term : Forecast → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ)
    (centerConstant : Forecast → ∀ j, J j → ℝ)
    (twists : ∀ f, Term f → NormalizedPolynomialTwist X (Σ j, J j)
      (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
      ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩)
    (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ Real.exp massLog)
    (happrox : ∀ f v, ‖forecast f v - ∑ i, coefficient f i *
      (twists f i).eval N (fun j => subtractConstant (centerConstant f j) (poly j)) v.val‖ ≤
        Real.exp (-(2 * u + 4 * p + 12)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass ((centeredFiniteMarginal μ law hweight).siteLaw physical) C ≤ εtail)
    (htail : εtail ≤ 6 * positiveProjectionAccuracy P)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Q := max commonBudget (2 * u + 4 * p + massLog + 20)
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (models : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, models i ∈ twistedNativeSampleFunctions (1 : X → ℕ) 0 commonBudget
        (fun u : integerBox N => u.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
          (u : integerBox N) => W.eval N poly u.val)) ∧
      input = (∑ i, coeff i • models i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (Q + 2) ∧
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical slices tests err ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).correlation err (forecast f)‖ ≤
        Real.exp (-u)) ∧
      (nterms : ℝ) ≤ Real.exp (2 * Q + 2 * u + 4 * p + 34) ∧
      ∀ errLocal : Center × Ω → ℂ, Measurable errLocal →
        (∀ center z, ∃ j, errLocal (center, z) =
          𝔼 t ∈ slices z j, err (physical z t) * tests z j t) →
        Integrable errLocal (centeredFiniteProbabilityMeasure μ law) ∧
          (∫ y, ‖errLocal y‖ ∂centeredFiniteProbabilityMeasure μ law) ≤ Real.exp (-u) := by
  intro commonBudget Q
  have hlocalCommon : localBudget ≤ commonBudget := le_max_left _ _
  have hcommon : 0 ≤ commonBudget := hlocalBudget.trans hlocalCommon
  obtain ⟨hQ, _, hcommonQ, hthreshold, hgain, _⟩ :=
    forecastAugmented_model_parameters hu hp hmassLog hcommon
  let shifted := fun f i => (twists f i).shiftConstant (centerConstant f)
  let atom := fun f i (v : integerBox N) => (shifted f i).eval N poly v.val
  have hatom (f) (i) : atom f i ∈
      twistedNativeSampleFunctions (1 : X → ℕ) 0 commonBudget
        (fun v : integerBox N => v.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩) v => W.eval N poly v.val) :=
    centeredForecastTwist_mem_common_family localBudget Pnative hPnative
      twists N poly centerConstant f i
  have happrox' (f) (v : integerBox N) :
      ‖forecast f v - ∑ i, coefficient f i * atom f i v‖ ≤
        forecastAugmentedUnitThreshold u p K C forecastCap / 8 := by
    have he := (happrox f v).trans (forecastAugmented_approximation_precision
      hu hp hK (zero_le_one.trans hC) hKp hCp hforecastCapP)
    change ‖forecast f v - ∑ i, coefficient f i *
      ((twists f i).shiftConstant (centerConstant f)).eval N poly v.val‖ ≤ _
    rw [centeredForecastTwist_sum_eq twists coefficient N poly centerConstant f v.val]
    exact he
  have hdetectCommon (signal : (X → ℤ) → ℂ)
      (hsignal : ∀ v, ‖signal v‖ ≤ 1)
      (hzero : ∀ v, v ∉ integerBox N → signal v = 0)
      (hlarge : forecastAugmentedUnitThreshold u p K C forecastCap ≤
        sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) site slices tests signal) :
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩) (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel (1 : X → ℕ) 0 commonBudget
          (fun v : integerBox N => v.val) G) ∧
        Real.exp (-Q) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun v => signal v.val)
          (fun v => star (W.eval N poly v.val) * G v)‖ := by
    obtain ⟨W, G, hG, hc⟩ := hdetect signal hsignal hzero hlarge
    have he : Real.exp localBudget ≤ Real.exp commonBudget := Real.exp_le_exp.mpr hlocalCommon
    let W' := W.mono he he
      (show (⟨Real.exp localBudget, Real.exp_nonneg _⟩ : ℝ≥0) ≤
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩ from he)
    refine ⟨W', G, hG.map (fun model => model.mono hlocalCommon), ?_⟩
    exact hgain.trans ((Real.exp_le_exp.mpr (neg_le_neg hlocalCommon)).trans hc)
  exact exists_averaged_normalizedTwist_forecast_joint_model N poly μ law hweight
    physical site hphysical slices tests (1 : X → ℕ) 0 commonBudget forecast
    hu hp hQ hmassLog hK hC hforecastCap hKp hCp hforecastCapP hthreshold hP
    hslices hsize htests hforecast hdetectCommon Term coefficient atom hatom
    (Real.exp_nonneg massLog) le_rfl hmass happrox' hexcess htail input hinput

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_fixedLaw_centered_forecast_twist_model (s : ℕ)
    {Ω T X Forecast : Type*} [Nonempty Forecast] [Fintype Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (localBudget Pnative : ℝ) (hlocalBudget : 0 ≤ localBudget) (hPnative : 0 ≤ Pnative)
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (law : FiniteProbabilityWeights Ω)
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (forecast : Forecast → integerBox N → ℂ)
    {u p P massLog K C forecastCap εtail : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hmassLog : 0 ≤ massLog)
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hforecastCapP : forecastCap ≤ Real.exp p)
    (hP : u + 2 * p +
      max (max localBudget (3 * Pnative + 3)) (2 * u + 4 * p + massLog + 20) + 32 ≤ P)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f u, ‖forecast f u‖ ≤ forecastCap)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ u, ‖signal u‖ ≤ 1) →
      (∀ u, u ∉ integerBox N → signal u = 0) →
      forecastAugmentedUnitThreshold u p K C forecastCap ≤
        sampledSliceSeminorm law site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp localBudget) (Real.exp localBudget)
          ⟨Real.exp localBudget, Real.exp_nonneg _⟩)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel (1 : X → ℕ) s localBudget
          (fun u : integerBox N => u.val) G) ∧
        Real.exp (-localBudget) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun u => signal u.val)
          (fun u => star (W.eval N poly u.val) * G u)‖)
    (Term : Forecast → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ)
    (centerConstant : Forecast → ∀ j, J j → ℝ)
    (twists : ∀ f, Term f → NormalizedPolynomialTwist X (Σ j, J j)
      (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
      ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩)
    (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ Real.exp massLog)
    (happrox : ∀ f v, ‖forecast f v - ∑ i, coefficient f i *
      (twists f i).eval N (fun j => subtractConstant (centerConstant f j) (poly j)) v.val‖ ≤
        Real.exp (-(2 * u + 4 * p + 12)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass (law.siteLaw physical) C ≤ εtail)
    (htail : εtail ≤ 6 * positiveProjectionAccuracy P)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Q := max commonBudget (2 * u + 4 * p + massLog + 20)
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (models : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, models i ∈ twistedNativeSampleFunctions (1 : X → ℕ) s commonBudget
        (fun u : integerBox N => u.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
          (u : integerBox N) => W.eval N poly u.val)) ∧
      input = (∑ i, coeff i • models i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (Q + 2) ∧
      sampledSliceSeminorm law physical slices tests err ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).correlation err (forecast f)‖ ≤
        Real.exp (-u)) ∧
      (nterms : ℝ) ≤ Real.exp (2 * Q + 2 * u + 4 * p + 34) := by
  intro commonBudget Q
  have hlocalCommon : localBudget ≤ commonBudget := le_max_left _ _
  have hcommon : 0 ≤ commonBudget := hlocalBudget.trans hlocalCommon
  obtain ⟨hQ, _, hcommonQ, hthreshold, hgain, _⟩ :=
    forecastAugmented_model_parameters hu hp hmassLog hcommon
  let shifted := fun f i => (twists f i).shiftConstant (centerConstant f)
  let atom := fun f i (v : integerBox N) => (shifted f i).eval N poly v.val
  have hatom (f) (i) : atom f i ∈
      twistedNativeSampleFunctions (1 : X → ℕ) s commonBudget
        (fun v : integerBox N => v.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩) v => W.eval N poly v.val) :=
    centeredForecastTwist_mem_common_family localBudget Pnative hPnative
      twists N poly centerConstant f i
  have happrox' (f) (v : integerBox N) :
      ‖forecast f v - ∑ i, coefficient f i * atom f i v‖ ≤
        forecastAugmentedUnitThreshold u p K C forecastCap / 8 := by
    have he := (happrox f v).trans (forecastAugmented_approximation_precision
      hu hp hK (zero_le_one.trans hC) hKp hCp hforecastCapP)
    change ‖forecast f v - ∑ i, coefficient f i *
      ((twists f i).shiftConstant (centerConstant f)).eval N poly v.val‖ ≤ _
    rw [centeredForecastTwist_sum_eq twists coefficient N poly centerConstant f v.val]
    exact he
  have hdetectCommon (signal : (X → ℤ) → ℂ)
      (hsignal : ∀ v, ‖signal v‖ ≤ 1)
      (hzero : ∀ v, v ∉ integerBox N → signal v = 0)
      (hlarge : forecastAugmentedUnitThreshold u p K C forecastCap ≤
        sampledSliceSeminorm law site slices tests signal) :
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩) (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel (1 : X → ℕ) s commonBudget
          (fun v : integerBox N => v.val) G) ∧
        Real.exp (-Q) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun v => signal v.val)
          (fun v => star (W.eval N poly v.val) * G v)‖ := by
    obtain ⟨W, G, hG, hc⟩ := hdetect signal hsignal hzero hlarge
    have he : Real.exp localBudget ≤ Real.exp commonBudget := Real.exp_le_exp.mpr hlocalCommon
    let W' := W.mono he he
      (show (⟨Real.exp localBudget, Real.exp_nonneg _⟩ : ℝ≥0) ≤
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩ from he)
    refine ⟨W', G, hG.map (fun model => model.mono hlocalCommon), ?_⟩
    exact hgain.trans ((Real.exp_le_exp.mpr (neg_le_neg hlocalCommon)).trans hc)
  exact exists_normalizedTwist_forecast_model N poly law
    physical site hphysical slices tests (1 : X → ℕ) s commonBudget forecast
    hu hp hQ hmassLog hK hC hforecastCap hKp hCp hforecastCapP hthreshold hP
    hsize htests hforecast hdetectCommon Term coefficient atom hatom
    (Real.exp_nonneg massLog) le_rfl hmass happrox' hexcess htail input hinput

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

structure ActualForecastData (N : X → ℕ)
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Pnative massLog capLog E : ℝ) where
  target : integerBox N → ℂ
  centerConstant : ∀ j, J j → ℝ
  Term : Type
  [fintypeTerm : Fintype Term]
  coefficient : Term → ℂ
  twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
    (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
    ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩
  cap : ∀ v, ‖target v‖ ≤ Real.exp capLog
  mass : (∑ i, ‖coefficient i‖) ≤ Real.exp massLog
  approximation : ∀ v, ‖target v - ∑ i, coefficient i *
    (twists i).eval N (fun j => subtractConstant (centerConstant j) (originalpoly j)) v.val‖ ≤
      Real.exp (-E)

attribute [instance] ActualForecastData.fintypeTerm

namespace ActualForecastData

variable (N : X → ℕ) (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (Pnative massLog capLog E : ℝ)

noncomputable def zero : ActualForecastData N originalpoly Pnative massLog capLog E where
  target := fun _ => 0
  centerConstant := fun _ _ => 0
  Term := Empty
  coefficient := fun i => nomatch i
  twists := fun i => nomatch i
  cap := fun _ => by simpa only [norm_zero] using Real.exp_nonneg capLog
  mass := by simpa using Real.exp_nonneg massLog
  approximation := fun _ => by simpa using Real.exp_nonneg (-E)

@[simp] theorem zero_target (v : integerBox N) :
    (zero N originalpoly Pnative massLog capLog E).target v = 0 := rfl

@[simp] theorem zero_centerConstant (j : Fin m) (i : J j) :
    (zero N originalpoly Pnative massLog capLog E).centerConstant j i = 0 := rfl

end ActualForecastData

variable {N : X → ℕ} {originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {Pnative massLog capLog E : ℝ} {F : Type*}

noncomputable def actualForecastOptionFamily
    (data : F → ActualForecastData N originalpoly Pnative massLog capLog E) :
    Option F → ActualForecastData N originalpoly Pnative massLog capLog E
  | none => ActualForecastData.zero N originalpoly Pnative massLog capLog E
  | some f => data f

@[simp] theorem actualForecastOptionFamily_some
    (data : F → ActualForecastData N originalpoly Pnative massLog capLog E) (f : F) :
    actualForecastOptionFamily data (some f) = data f := rfl

@[simp] theorem actualForecastOptionFamily_none_target
    (data : F → ActualForecastData N originalpoly Pnative massLog capLog E)
    (v : integerBox N) : (actualForecastOptionFamily data none).target v = 0 := rfl

@[simp] theorem actualForecastOptionFamily_none_centerConstant
    (data : F → ActualForecastData N originalpoly Pnative massLog capLog E)
    (j : Fin m) (i : J j) :
    (actualForecastOptionFamily data none).centerConstant j i = 0 := rfl

theorem actualForecastOptionFamily_bounds
    (data : F → ActualForecastData N originalpoly Pnative massLog capLog E) :
    (∀ f v, ‖(actualForecastOptionFamily data f).target v‖ ≤ Real.exp capLog) ∧
    (∀ f, (∑ i, ‖(actualForecastOptionFamily data f).coefficient i‖) ≤ Real.exp massLog) ∧
    (∀ f v, ‖(actualForecastOptionFamily data f).target v -
      ∑ i, (actualForecastOptionFamily data f).coefficient i *
        ((actualForecastOptionFamily data f).twists i).eval N
          (fun j => subtractConstant ((actualForecastOptionFamily data f).centerConstant j)
            (originalpoly j)) v.val‖ ≤ Real.exp (-E)) :=
  ⟨fun f => (actualForecastOptionFamily data f).cap,
    fun f => (actualForecastOptionFamily data f).mass,
    fun f => (actualForecastOptionFamily data f).approximation⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.ActualForecastData
open scoped BigOperators NNReal

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {N : X → ℕ} {originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {Pnative massLog capLog E : ℝ}
variable (data : ActualForecastData N originalpoly Pnative massLog capLog E)

theorem native_product_lipschitz_bound
    (_data : ActualForecastData N originalpoly Pnative massLog capLog E)
    {pw cw Ptest : ℝ} {Lw : ℝ≥0}
    (_W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (hPtest : 0 ≤ Ptest) (hLw : (Lw : ℝ) ≤ Real.exp Ptest)
    (hcw : cw ≤ Real.exp Ptest) :
    ((Lw * max 1 (Real.toNNReal (Real.exp (3 * Pnative + 3))) +
      ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩ * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤
      Real.exp (2 * max Ptest (3 * Pnative + 3) + 1) := by
  let P := max Ptest (3 * Pnative + 3)
  have hP : 0 ≤ P := hPtest.trans (le_max_left _ _)
  have ht : Real.exp Ptest ≤ Real.exp P := Real.exp_le_exp.mpr (le_max_left _ _)
  have hn : Real.exp (3 * Pnative + 3) ≤ Real.exp P :=
    Real.exp_le_exp.mpr (le_max_right _ _)
  have hmax {c : ℝ} (hc : c ≤ Real.exp P) :
      ((max 1 (Real.toNNReal c) : ℝ≥0) : ℝ) ≤ Real.exp P := by
    simp only [NNReal.coe_max, NNReal.coe_one]
    exact max_le (Real.one_le_exp hP) (max_le hc (Real.exp_pos _).le)
  have h1 := mul_le_mul (hLw.trans ht) (hmax hn)
    (NNReal.coe_nonneg (max 1 (Real.toNNReal (Real.exp (3 * Pnative + 3)))))
    (Real.exp_pos P).le
  have h2 := mul_le_mul hn (hmax (hcw.trans ht))
    (NNReal.coe_nonneg (max 1 (Real.toNNReal cw))) (Real.exp_pos P).le
  have he : Real.exp P * Real.exp P = Real.exp (2 * P) := by
    rw [← Real.exp_add]; congr 1; ring
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp (1 : ℝ) using 1; norm_num
  calc
    _ ≤ 2 * Real.exp (2 * P) := by
      change (Lw : ℝ) * ((max 1 (Real.toNNReal (Real.exp (3 * Pnative + 3))) : ℝ≥0) : ℝ) +
        Real.exp (3 * Pnative + 3) * ((max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤ _
      rw [he] at h1 h2
      linarith
    _ ≤ Real.exp 1 * Real.exp (2 * P) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [P]; ring

theorem native_product_bounds
    {pw cw Ptest : ℝ} {Lw : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (hPtest : 0 ≤ Ptest) (hLw : (Lw : ℝ) ≤ Real.exp Ptest)
    (hpw : pw ≤ Real.exp Ptest) (hcw : cw ≤ Real.exp Ptest) :
    let P := max Ptest (3 * Pnative + 3)
    ∀ i : data.Term,
      ((Lw * max 1 (Real.toNNReal (Real.exp (3 * Pnative + 3))) +
        ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩ * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤
          Real.exp (2 * P + 1) ∧
      ((W.cover * (data.twists i).cover : ℕ) : ℝ) ≤ Real.exp (2 * P + 1) ∧
      ((W.modulus * (data.twists i).modulus : ℕ) : ℝ) ≤ Real.exp (2 * P + 1) := by
  intro P i
  have ht : Real.exp Ptest ≤ Real.exp P := Real.exp_le_exp.mpr (le_max_left _ _)
  have hn : Real.exp (3 * Pnative + 3) ≤ Real.exp P := Real.exp_le_exp.mpr (le_max_right _ _)
  exact W.productUniform_exp_bounds (data.twists i) (hPtest.trans (le_max_left _ _))
    (hLw.trans ht) hn (hpw.trans ht) (hcw.trans ht) hn hn

end Erdos3.VectorPolynomial.ActualForecastData

end

end OAI

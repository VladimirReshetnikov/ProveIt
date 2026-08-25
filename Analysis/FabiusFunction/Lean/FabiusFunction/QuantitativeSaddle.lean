import FabiusFunction.BromwichSaddle
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Quantitative Gaussian extraction for saddle-point integrals

This module isolates the measure-theoretic end of a quantitative saddle-point
argument.  After rescaling, a kernel is compared with an integrable reference
of Gaussian mass.  Bounds on a measurable central set and its complement give
the relative estimate `1 + O(1 / b)`.

At this precision one must normally retain the first odd correction: its
absolute integral is `O(1 / √b)`, although its signed integral vanishes.  The
theorem `normalized_integral_sub_one_isBigO_of_central_tail_odd_correction`
makes that cancellation explicit.  The generic
`normalized_integral_sub_reference_isBigO_of_L1` and central/tail companion
isolate the preceding passage from kernel error to normalized-integral error.
None of these results hides a derivative, product, or tail estimate specific
to the Fabius function.
-/

set_option autoImplicit false

open Filter MeasureTheory Set Asymptotics
open scoped Topology

namespace Fabius.QuantitativeSaddle

/-- The real standard Gaussian, regarded as a complex-valued function. -/
noncomputable def standardGaussian (v : ℝ) : ℂ :=
  (Real.exp (-(v ^ 2) / 2) : ℝ)

/-- The complex-valued standard Gaussian `exp (-v ^ 2 / 2)` is Lebesgue
integrable on the whole real line. -/
lemma integrable_standardGaussian : Integrable standardGaussian := by
  have hreal : Integrable (fun v : ℝ => Real.exp (-(1 / 2 : ℝ) * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hcomplex : Integrable
      (fun v : ℝ => (Real.exp (-(1 / 2 : ℝ) * v ^ 2) : ℂ)) :=
    hreal.ofReal
  apply hcomplex.congr
  filter_upwards with v
  simp only [standardGaussian]
  congr 2
  ring

/-- The total mass of `standardGaussian` is `Real.sqrt (2 * Real.pi)`: the
weight `exp (-v ^ 2 / 2)` carries no normalizing prefactor.  Within this file
it is used only to evaluate the reference mass in
`normalized_integral_sub_one_isBigO_of_central_tail_odd_correction`. -/
lemma integral_standardGaussian :
    (∫ v : ℝ, standardGaussian v) =
      (Real.sqrt (2 * Real.pi) : ℂ) := by
  change (∫ v : ℝ, (Real.exp (-(v ^ 2) / 2) : ℂ)) = _
  have heq : (fun v : ℝ => (Real.exp (-(v ^ 2) / 2) : ℂ)) =
      fun v : ℝ => (Real.exp (-(1 / 2 : ℝ) * v ^ 2) : ℂ) := by
    funext v
    congr 2
    ring
  rw [heq]
  have hreal :
      (∫ v : ℝ, Real.exp (-(1 / 2 : ℝ) * v ^ 2)) =
        Real.sqrt (2 * Real.pi) := by
    rw [integral_gaussian]
    congr 1
    ring
  exact_mod_cast hreal

/-- An odd function with values in a complete real normed additive group has
zero Lebesgue integral on the real line.  Mathlib defines the integral of a
nonintegrable function to be zero, so integrability is not required for this
identity. -/
lemma integral_eq_zero_of_odd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (J : ℝ → E) (hodd : Function.Odd J) :
    (∫ v : ℝ, J v) = 0 := by
  have hinvariant := integral_neg_eq_self J volume
  have hfun : (fun v : ℝ => J (-v)) = -J := by
    funext v
    exact hodd v
  rw [hfun, integral_neg'] at hinvariant
  have hsum : (∫ v : ℝ, J v) + ∫ v : ℝ, J v = 0 :=
    eq_neg_iff_add_eq_zero.mp hinvariant.symm
  have hsmul : (2 : ℝ) • (∫ v : ℝ, J v) = 0 := by
    simpa only [two_smul ℝ] using hsum
  exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)

/-- Integrate a pointwise norm bound for the difference of two Bochner
integrable functions with values in any complete real normed additive
group. -/
theorem norm_integral_sub_le_of_pointwise
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (K G : ℝ → E) (g : ℝ → ℝ)
    (hK : Integrable K) (hG : Integrable G) (hg : Integrable g)
    (hbound : ∀ v : ℝ, ‖K v - G v‖ ≤ g v) :
    ‖(∫ v : ℝ, K v) - ∫ v : ℝ, G v‖ ≤ ∫ v : ℝ, g v := by
  rw [← integral_sub hK hG]
  exact norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hbound)

/-- An `L¹` approximation of a complex kernel by any integrable reference
gives the same-order approximation of their Gaussian-normalized integrals.
The comparison rate and indexing filter are completely arbitrary. -/
theorem normalized_integral_sub_reference_isBigO_of_L1
    {α : Type*} (l : Filter α) (rate : α → ℝ)
    (K reference : α → ℝ → ℂ)
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hreference : ∀ᶠ i in l, Integrable (reference i))
    (herror : (fun i => ∫ v : ℝ, ‖K i v - reference i v‖) =O[l] rate) :
    (fun i =>
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (∫ v : ℝ, K i v) -
        (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
          (∫ v : ℝ, reference i v)) =O[l] rate := by
  rw [isBigO_iff] at herror ⊢
  obtain ⟨C, hC⟩ := herror
  let gaussianMass : ℝ := Real.sqrt (2 * Real.pi)
  have hmass : 0 < gaussianMass := by
    dsimp [gaussianMass]
    positivity
  refine ⟨gaussianMass⁻¹ * C, ?_⟩
  filter_upwards [hK, hreference, hC] with i hKi hRi hi
  have hdiffInt : Integrable (fun v => ‖K i v - reference i v‖) :=
    (hKi.sub hRi).norm
  have hnonneg : 0 ≤ ∫ v : ℝ, ‖K i v - reference i v‖ :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hi
  have hnorm := norm_integral_sub_le_of_pointwise (K i) (reference i)
    (fun v => ‖K i v - reference i v‖) hKi hRi hdiffInt
    (fun _ => le_rfl)
  change ‖(gaussianMass : ℂ)⁻¹ * (∫ v : ℝ, K i v) -
      (gaussianMass : ℂ)⁻¹ * (∫ v : ℝ, reference i v)‖ ≤ _
  rw [← mul_sub, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hmass]
  calc
    gaussianMass⁻¹ *
          ‖(∫ v : ℝ, K i v) - ∫ v : ℝ, reference i v‖
        ≤ gaussianMass⁻¹ *
          (∫ v : ℝ, ‖K i v - reference i v‖) := by gcongr
    _ ≤ gaussianMass⁻¹ * (C * ‖rate i‖) := by gcongr
    _ = (gaussianMass⁻¹ * C) * ‖rate i‖ := by ring

/-- Central-set plus complementary-tail form of the arbitrary-reference
normalized-integral estimate. -/
theorem normalized_integral_sub_reference_isBigO_of_central_tail
    {α : Type*} (l : Filter α) (rate : α → ℝ)
    (K reference : α → ℝ → ℂ) (central : α → Set ℝ)
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hreference : ∀ᶠ i in l, Integrable (reference i))
    (hcentralMeas : ∀ᶠ i in l, MeasurableSet (central i))
    (hcentral :
      (fun i => ∫ v in central i, ‖K i v - reference i v‖) =O[l] rate)
    (htail :
      (fun i => ∫ v in (central i)ᶜ, ‖K i v - reference i v‖) =O[l] rate) :
    (fun i =>
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (∫ v : ℝ, K i v) -
        (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
          (∫ v : ℝ, reference i v)) =O[l] rate := by
  apply normalized_integral_sub_reference_isBigO_of_L1 l rate K reference
    hK hreference
  have hsum := hcentral.add htail
  apply hsum.congr'
  · filter_upwards [hK, hreference, hcentralMeas] with i hKi hRi hmeas
    have hdiffInt : Integrable (fun v => ‖K i v - reference i v‖) :=
      (hKi.sub hRi).norm
    exact integral_add_compl hmeas hdiffInt
  · exact Filter.EventuallyEq.rfl

/-- If the reference has standard Gaussian mass, an `L¹` approximation gives
the same-order relative estimate `normalized integral = 1 + O(rate)`. -/
theorem normalized_integral_sub_one_isBigO_of_L1
    {α : Type*} (l : Filter α) (rate : α → ℝ)
    (K reference : α → ℝ → ℂ)
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hreference : ∀ᶠ i in l, Integrable (reference i))
    (hreferenceMass : ∀ᶠ i in l,
      (∫ v : ℝ, reference i v) = (Real.sqrt (2 * Real.pi) : ℂ))
    (herror : (fun i => ∫ v : ℝ, ‖K i v - reference i v‖) =O[l] rate) :
    (fun i =>
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (∫ v : ℝ, K i v) - 1)
        =O[l] rate := by
  have h := normalized_integral_sub_reference_isBigO_of_L1
    l rate K reference hK hreference herror
  apply h.congr'
  · filter_upwards [hreferenceMass] with i hi
    rw [hi]
    have hmass : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (by positivity : 0 < Real.sqrt (2 * Real.pi)))
    rw [inv_mul_cancel₀ hmass]
  · exact Filter.EventuallyEq.rfl

/-- Central-set plus complementary-tail form of
`normalized_integral_sub_one_isBigO_of_L1`. -/
theorem normalized_integral_sub_one_isBigO_of_central_tail
    {α : Type*} (l : Filter α) (rate : α → ℝ)
    (K reference : α → ℝ → ℂ) (central : α → Set ℝ)
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hreference : ∀ᶠ i in l, Integrable (reference i))
    (hreferenceMass : ∀ᶠ i in l,
      (∫ v : ℝ, reference i v) = (Real.sqrt (2 * Real.pi) : ℂ))
    (hcentralMeas : ∀ᶠ i in l, MeasurableSet (central i))
    (hcentral :
      (fun i => ∫ v in central i, ‖K i v - reference i v‖) =O[l] rate)
    (htail :
      (fun i => ∫ v in (central i)ᶜ, ‖K i v - reference i v‖) =O[l] rate) :
    (fun i =>
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (∫ v : ℝ, K i v) - 1)
        =O[l] rate := by
  have h := normalized_integral_sub_reference_isBigO_of_central_tail
    l rate K reference central hK hreference hcentralMeas hcentral htail
  apply h.congr'
  · filter_upwards [hreferenceMass] with i hi
    rw [hi]
    have hmass : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (by positivity : 0 < Real.sqrt (2 * Real.pi)))
    rw [inv_mul_cancel₀ hmass]
  · exact Filter.EventuallyEq.rfl

/-- A normalized integral is `1 + O(1 / b)` if its kernel has `L¹` distance
`O(1 / b)` from an integrable reference of standard Gaussian mass. -/
theorem normalized_integral_sub_one_isBigO_of_reference
    {α : Type*} (l : Filter α) (b : α → ℝ)
    (K reference : α → ℝ → ℂ) (C : ℝ)
    (hb : ∀ᶠ i in l, 0 < b i)
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hreference : ∀ᶠ i in l, Integrable (reference i))
    (hreferenceMass : ∀ᶠ i in l,
      (∫ v : ℝ, reference i v) = (Real.sqrt (2 * Real.pi) : ℂ))
    (herror : ∀ᶠ i in l,
      (∫ v : ℝ, ‖K i v - reference i v‖) ≤ C * (b i)⁻¹) :
    (fun i =>
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (∫ v : ℝ, K i v) - 1) =O[l]
        (fun i => (b i)⁻¹) := by
  apply normalized_integral_sub_one_isBigO_of_L1 l
    (fun i => (b i)⁻¹) K reference hK hreference hreferenceMass
  apply IsBigO.of_bound C
  filter_upwards [hb, herror] with i hbi hi
  have hnonneg : 0 ≤ ∫ v : ℝ, ‖K i v - reference i v‖ :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hbi)]
  exact hi

/-- Central-arc plus complementary-tail form of quantitative Gaussian
extraction, relative to any reference kernel of standard Gaussian mass. -/
theorem normalized_integral_sub_one_isBigO_of_central_tail_reference
    {α : Type*} (l : Filter α) (b : α → ℝ)
    (K reference : α → ℝ → ℂ) (central : α → Set ℝ)
    (Ccentral Ctail : ℝ)
    (hb : ∀ᶠ i in l, 0 < b i)
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hreference : ∀ᶠ i in l, Integrable (reference i))
    (hreferenceMass : ∀ᶠ i in l,
      (∫ v : ℝ, reference i v) = (Real.sqrt (2 * Real.pi) : ℂ))
    (hcentralMeas : ∀ᶠ i in l, MeasurableSet (central i))
    (hcentral : ∀ᶠ i in l,
      (∫ v in central i, ‖K i v - reference i v‖) ≤
        Ccentral * (b i)⁻¹)
    (htail : ∀ᶠ i in l,
      (∫ v in (central i)ᶜ, ‖K i v - reference i v‖) ≤
        Ctail * (b i)⁻¹) :
    (fun i =>
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (∫ v : ℝ, K i v) - 1) =O[l]
        (fun i => (b i)⁻¹) := by
  apply normalized_integral_sub_one_isBigO_of_central_tail l
    (fun i => (b i)⁻¹) K reference central hK hreference hreferenceMass
    hcentralMeas
  · apply IsBigO.of_bound Ccentral
    filter_upwards [hb, hcentral] with i hbi hi
    have hnonneg : 0 ≤ ∫ v in central i, ‖K i v - reference i v‖ :=
      integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hbi)]
    exact hi
  · apply IsBigO.of_bound Ctail
    filter_upwards [hb, htail] with i hbi hi
    have hnonneg : 0 ≤ ∫ v in (central i)ᶜ,
        ‖K i v - reference i v‖ :=
      integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hbi)]
    exact hi

/-- The saddle-point specialization which retains an integrable odd first
correction `J`.  Its integral vanishes, while the two hypotheses bound the
corrected error on the central arc and its complement. -/
theorem normalized_integral_sub_one_isBigO_of_central_tail_odd_correction
    {α : Type*} (l : Filter α) (b : α → ℝ) (K J : α → ℝ → ℂ)
    (central : α → Set ℝ) (Ccentral Ctail : ℝ)
    (hb : ∀ᶠ i in l, 0 < b i)
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hJ : ∀ᶠ i in l, Integrable (J i))
    (hJodd : ∀ᶠ i in l, Function.Odd (J i))
    (hcentralMeas : ∀ᶠ i in l, MeasurableSet (central i))
    (hcentral : ∀ᶠ i in l,
      (∫ v in central i,
        ‖K i v - (standardGaussian v + J i v)‖) ≤
          Ccentral * (b i)⁻¹)
    (htail : ∀ᶠ i in l,
      (∫ v in (central i)ᶜ,
        ‖K i v - (standardGaussian v + J i v)‖) ≤
          Ctail * (b i)⁻¹) :
    (fun i =>
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (∫ v : ℝ, K i v) - 1) =O[l]
        (fun i => (b i)⁻¹) := by
  let reference : α → ℝ → ℂ := fun i v => standardGaussian v + J i v
  apply normalized_integral_sub_one_isBigO_of_central_tail_reference
    l b K reference central Ccentral Ctail hb hK
  · filter_upwards [hJ] with i hJi
    exact integrable_standardGaussian.add hJi
  · filter_upwards [hJ, hJodd] with i hJi hodd
    dsimp [reference]
    rw [integral_add integrable_standardGaussian hJi,
      integral_standardGaussian, integral_eq_zero_of_odd (J i) hodd, add_zero]
  · exact hcentralMeas
  · filter_upwards [hcentral] with i hi
    simpa only [reference] using hi
  · filter_upwards [htail] with i hi
    simpa only [reference] using hi

/-- A quantity tending to `1` which is `1 + O(h)` has logarithm `O(h)`. -/
theorem real_log_of_relative_error_isBigO
    {α : Type*} (l : Filter α) (ratio h : α → ℝ)
    (hratio : Tendsto ratio l (𝓝 1))
    (hrelative : (fun i => ratio i - 1) =O[l] h) :
    (fun i => Real.log (ratio i)) =O[l] h := by
  have hlocal :=
    (Real.hasDerivAt_log one_ne_zero).isBigO_sub.comp_tendsto hratio
  have hcomposed :
      (fun i => Real.log (ratio i) - Real.log 1) =O[l]
        (fun i => ratio i - 1) := by
    simpa only [Function.comp_def] using hlocal
  simpa only [Real.log_one, sub_zero] using hcomposed.trans hrelative

/-- Relative `1 + O(1 / b)` implies logarithmic `O(1 / b)` when `b` tends to
infinity. -/
theorem real_log_of_relative_error_isBigO_inv
    {α : Type*} (l : Filter α) (b ratio : α → ℝ)
    (hb : Tendsto b l atTop)
    (hrelative : (fun i => ratio i - 1) =O[l] (fun i => (b i)⁻¹)) :
    (fun i => Real.log (ratio i)) =O[l] (fun i => (b i)⁻¹) := by
  have hinv : Tendsto (fun i => (b i)⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hb
  have hzero : Tendsto (fun i => ratio i - 1) l (𝓝 0) :=
    hrelative.trans_tendsto hinv
  have hratio : Tendsto ratio l (𝓝 1) := by
    have hadd := hzero.add_const 1
    convert hadd using 1 <;> simp
  exact real_log_of_relative_error_isBigO l ratio (fun i => (b i)⁻¹)
    hratio hrelative

/-- If `A / M = 1 + O(1 / b)` and both terms are eventually nonzero, then
`log A - log M = O(1 / b)`. -/
theorem real_log_sub_log_isBigO_inv
    {α : Type*} (l : Filter α) (b A M : α → ℝ)
    (hb : Tendsto b l atTop)
    (hA : ∀ᶠ i in l, A i ≠ 0)
    (hM : ∀ᶠ i in l, M i ≠ 0)
    (hrelative : (fun i => A i / M i - 1) =O[l] (fun i => (b i)⁻¹)) :
    (fun i => Real.log (A i) - Real.log (M i)) =O[l]
      (fun i => (b i)⁻¹) := by
  have hlog := real_log_of_relative_error_isBigO_inv l b
    (fun i => A i / M i) hb hrelative
  apply hlog.congr'
  · filter_upwards [hA, hM] with i hAi hMi
    exact Real.log_div hAi hMi
  · exact Filter.EventuallyEq.rfl

end Fabius.QuantitativeSaddle

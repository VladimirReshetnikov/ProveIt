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
makes that cancellation explicit.  It does not hide any derivative, product,
or tail estimate specific to the Fabius function.
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

/-- A complex-valued odd function has zero Lebesgue integral on the real
line.  Mathlib defines the integral of a nonintegrable function to be zero, so
integrability is not required for this identity. -/
lemma integral_eq_zero_of_odd (J : ℝ → ℂ) (hodd : Function.Odd J) :
    (∫ v : ℝ, J v) = 0 := by
  have hinvariant := integral_neg_eq_self J volume
  have hfun : (fun v : ℝ => J (-v)) = -J := by
    funext v
    exact hodd v
  rw [hfun, integral_neg'] at hinvariant
  exact neg_eq_self.mp hinvariant

/-- Integrate a pointwise norm bound for the difference of two Bochner
integrable functions. -/
theorem norm_integral_sub_le_of_pointwise
    (K G : ℝ → ℂ) (g : ℝ → ℝ)
    (hK : Integrable K) (hG : Integrable G) (hg : Integrable g)
    (hbound : ∀ v : ℝ, ‖K v - G v‖ ≤ g v) :
    ‖(∫ v : ℝ, K v) - ∫ v : ℝ, G v‖ ≤ ∫ v : ℝ, g v := by
  rw [← integral_sub hK hG]
  exact norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hbound)

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
  rw [isBigO_iff]
  let gaussianMass : ℝ := Real.sqrt (2 * Real.pi)
  have hmass : 0 < gaussianMass := by
    dsimp [gaussianMass]
    positivity
  refine ⟨C / gaussianMass, ?_⟩
  filter_upwards [hb, hK, hreference, hreferenceMass, herror] with
    i hbi hKi hRi hRmass herr
  have hdiffInt : Integrable (fun v => ‖K i v - reference i v‖) :=
    (hKi.sub hRi).norm
  have hdiff := norm_integral_sub_le_of_pointwise (K i) (reference i)
    (fun v => ‖K i v - reference i v‖) hKi hRi hdiffInt
    (fun _ => le_rfl)
  rw [hRmass] at hdiff
  change ‖(gaussianMass : ℂ)⁻¹ * (∫ v : ℝ, K i v) - 1‖ ≤ _
  have hrewrite :
      (gaussianMass : ℂ)⁻¹ * (∫ v : ℝ, K i v) - 1 =
        (gaussianMass : ℂ)⁻¹ *
          ((∫ v : ℝ, K i v) - (gaussianMass : ℂ)) := by
    field_simp [ne_of_gt hmass]
  rw [hrewrite, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hmass]
  have hbinv : ‖(b i)⁻¹‖ = (b i)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbi)]
  rw [hbinv]
  calc
    gaussianMass⁻¹ * ‖(∫ v : ℝ, K i v) - (gaussianMass : ℂ)‖
        ≤ gaussianMass⁻¹ * (∫ v : ℝ, ‖K i v - reference i v‖) := by
          gcongr
    _ ≤ gaussianMass⁻¹ * (C * (b i)⁻¹) := by
          gcongr
    _ = (C / gaussianMass) * (b i)⁻¹ := by ring

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
  apply normalized_integral_sub_one_isBigO_of_reference l b K reference
    (Ccentral + Ctail) hb hK hreference hreferenceMass
  filter_upwards [hK, hreference, hcentralMeas, hcentral, htail] with
    i hKi hRi hmeas hc ht
  have hdiffInt : Integrable (fun v => ‖K i v - reference i v‖) :=
    (hKi.sub hRi).norm
  rw [← integral_add_compl hmeas hdiffInt]
  calc
    (∫ v in central i, ‖K i v - reference i v‖) +
          ∫ v in (central i)ᶜ, ‖K i v - reference i v‖
        ≤ Ccentral * (b i)⁻¹ + Ctail * (b i)⁻¹ := add_le_add hc ht
    _ = (Ccentral + Ctail) * (b i)⁻¹ := by ring

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

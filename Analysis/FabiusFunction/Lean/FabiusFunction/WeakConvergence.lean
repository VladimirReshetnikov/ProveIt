import FabiusFunction.EarlyApproximants
import FabiusFunction.FourierProduct
import FabiusFunction.PaperStatements
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Weak convergence of the finite convolution approximants

This module proves Lemma 1 of Arias de Reyna's *An infinitely differentiable
function with compact support: definition and properties*.  In the paper's
notation, the finite measures `mu_n` converge weak-* to `phi * lambda`, where
`phi` is Rvachev's up function and `lambda` is Lebesgue measure.

We formalize weak-* convergence as convergence in the standard weak topology
on `ProbabilityMeasure ℝ`.  Explicit equivalent formulations are supplied
for bounded continuous test functions valued in an arbitrary `RCLike` field,
with convenient real and complex specializations.

The limiting density measure is also described intrinsically: every open set
meeting `(-1,1)` has positive mass, and its exact measure-theoretic support is
the closed interval `[-1,1]`.  Thus the endpoint inclusion is not merely a
consequence of a convenient closed support bound; both endpoints genuinely
belong to the topological support.

The index `n` here is the paper's finite cutoff: `finiteConvolutionMeasure n`
contains the factors indexed by `k = 1, ..., n`.  Internally those factors are
stored with zero-based indices, so its characteristic function contains
`cos (t / 2^(k+2))^(k+1)` for `k = 0, ..., n-1`.
-/

set_option autoImplicit false

open scoped BigOperators ENNReal MeasureTheory Topology BoundedContinuousFunction
open Filter Finset MeasureTheory Set
open Asymptotics

namespace Fabius

noncomputable section

/-- Rvachev's up function is integrable. -/
theorem rvachevUp_integrable (F : BoundedFabius) (hF : IsFabius F) :
    Integrable (rvachevUp F) := by
  apply (rvachev_contDiff F hF).continuous.integrable_of_hasCompactSupport
  exact rvachevUp_hasCompactSupport F hF

-- The companion fact "Rvachev's up function has total integral one" is
-- `Fabius.integral_rvachev_eq_one` in `FabiusFunction.AnalyticMoments` (reachable
-- here through `FabiusFunction.FourierProduct`).  It used to be restated in this
-- file as `integral_rvachevUp_eq_one`, proved from `moment_eq_integral_formula
-- F hF 0` — whose own `n = 0` branch is discharged by `integral_rvachev_eq_one`,
-- so that restatement was a round trip back to the theorem it duplicated.

/-- The density measure `φ λ` occurring in Lemma 1. -/
noncomputable def rvachevMeasure (F : BoundedFabius) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (rvachevUp F x))

/-- The density `rvachevMeasure F` is a probability measure whenever `F`
satisfies the Fabius equations. -/
theorem rvachevMeasure_isProbability (F : BoundedFabius) (hF : IsFabius F) :
    IsProbabilityMeasure (rvachevMeasure F) := by
  rw [isProbabilityMeasure_iff]
  unfold rvachevMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (rvachevUp_integrable F hF)
    (Eventually.of_forall (rvachevUp_nonneg F))]
  rw [integral_rvachev_eq_one F hF]
  norm_num

/-- The density measure has total mass one. -/
@[simp]
theorem rvachevMeasure_univ (F : BoundedFabius) (hF : IsFabius F) :
    rvachevMeasure F Set.univ = 1 := by
  letI := rvachevMeasure_isProbability F hF
  exact measure_univ

/-- The density measure assigns no mass outside the support interval. -/
@[simp]
theorem rvachevMeasure_compl_Icc (F : BoundedFabius) (hF : IsFabius F) :
    rvachevMeasure F ((Icc (-1 : ℝ) 1)ᶜ) = 0 := by
  rw [rvachevMeasure, withDensity_apply _ measurableSet_Icc.compl]
  apply setLIntegral_eq_zero measurableSet_Icc.compl
  intro x hx
  change ENNReal.ofReal (rvachevUp F x) = 0
  rw [rvachevUp_eq_zero_of_not_mem_Ioo F hF]
  · simp
  · intro hxIoo
    exact hx ⟨hxIoo.1.le, hxIoo.2.le⟩

/-- The density measure gives full mass to Rvachev's support interval. -/
@[simp]
theorem rvachevMeasure_Icc (F : BoundedFabius) (hF : IsFabius F) :
    rvachevMeasure F (Icc (-1 : ℝ) 1) = 1 := by
  have h := measure_add_measure_compl (s := Icc (-1 : ℝ) 1)
    (μ := rvachevMeasure F) measurableSet_Icc
  rw [rvachevMeasure_compl_Icc F hF, rvachevMeasure_univ F hF, add_zero] at h
  exact h

/-- Every open set that meets the interior `(-1,1)` of Rvachev's support has
positive `rvachevMeasure` mass.  This is the measure-level form of strict
positivity of the density on its ordinary support. -/
theorem rvachevMeasure_pos_of_isOpen_inter_Ioo
    (F : BoundedFabius) (hF : IsFabius F) {U : Set ℝ}
    (hU : IsOpen U) (hne : (U ∩ Ioo (-1 : ℝ) 1).Nonempty) :
    0 < rvachevMeasure F U := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hdensity : Measurable (fun x : ℝ => ENNReal.ofReal (rvachevUp F x)) :=
    ENNReal.measurable_ofReal.comp (rvachev_contDiff F hF).continuous.measurable
  have hnull :
      volume ({x : ℝ | ENNReal.ofReal (rvachevUp F x) ≠ 0} ∩ U) = 0 :=
    (withDensity_apply_eq_zero hdensity).mp (by
      simpa only [rvachevMeasure] using hzero)
  have hsub : U ∩ Ioo (-1 : ℝ) 1 ⊆
      {x : ℝ | ENNReal.ofReal (rvachevUp F x) ≠ 0} ∩ U := by
    intro x hx
    exact ⟨(ENNReal.ofReal_pos.mpr
      (rvachevUp_pos_of_mem_Ioo F hF hx.2)).ne', hx.1⟩
  have hVzero : volume (U ∩ Ioo (-1 : ℝ) 1) = 0 :=
    measure_mono_null hsub hnull
  exact ((hU.inter isOpen_Ioo).measure_pos volume hne).ne' hVzero

/-- The exact topological support of the Rvachev density measure is the closed
interval `[-1,1]`.  Although the density vanishes at the two endpoints, every
endpoint neighborhood meets the open positivity set `(-1,1)` and therefore
has positive mass. -/
theorem support_rvachevMeasure (F : BoundedFabius) (hF : IsFabius F) :
    (rvachevMeasure F).support = Icc (-1 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed isClosed_Icc
    rw [mem_ae_iff]
    exact rvachevMeasure_compl_Icc F hF
  · intro x hx
    rw [Measure.mem_support_iff_forall]
    intro U hUnhds
    obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hUnhds
    have hxClosure : x ∈ closure (Ioo (-1 : ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
      exact hx
    obtain ⟨y, hyV, hyIoo⟩ := mem_closure_iff.mp hxClosure V hVopen hxV
    exact (rvachevMeasure_pos_of_isOpen_inter_Ioo F hF hVopen
      ⟨y, hyV, hyIoo⟩).trans_le (measure_mono hVU)

/-- The characteristic function of the density `φ λ`, with the conversion
between mathlib's convention and the paper's Fourier-transform convention. -/
theorem rvachevMeasure_charFun (F : BoundedFabius) (hF : IsFabius F) (t : ℝ) :
    charFun (rvachevMeasure F) t =
      rvachevFourier F (-(t : ℂ) / (2 * Real.pi)) := by
  unfold charFun rvachevMeasure rvachevFourier
  rw [integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (rvachevUp_nonneg F x)]
    simp only [Real.inner_apply, Complex.real_smul]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  · exact ENNReal.measurable_ofReal.comp (rvachev_contDiff F hF).continuous.measurable
  · exact Eventually.of_forall fun x => ENNReal.ofReal_lt_top

/-- The finite cosine product which is the characteristic function of `μ_n`. -/
noncomputable def finiteCosineProduct (n : ℕ) (t : ℝ) : ℂ :=
  ∏ k ∈ range n, Complex.cos ((t : ℂ) / (2 : ℂ) ^ (k + 2)) ^ (k + 1)

/-- The final sinc factor in the finite telescoping identity. -/
noncomputable def sincTail (n : ℕ) (t : ℝ) : ℂ :=
  complexSinc ((t : ℂ) / (2 : ℂ) ^ (n + 1))

/-- Extending the cutoff appends the next weighted cosine factor. -/
theorem finiteCosineProduct_succ (n : ℕ) (t : ℝ) :
    finiteCosineProduct (n + 1) t = finiteCosineProduct n t *
      Complex.cos ((t : ℂ) / (2 : ℂ) ^ (n + 2)) ^ (n + 1) := by
  simp [finiteCosineProduct, prod_range_succ]

/-- The finite telescoping identity behind the proof of Lemma 1. -/
theorem finiteCosineProduct_mul_sincTail_pow (n : ℕ) (t : ℝ) :
    finiteCosineProduct n t * sincTail n t ^ n =
      ∏ k ∈ range n, complexSinc ((t : ℂ) / (2 : ℂ) ^ (k + 1)) := by
  induction n with
  | zero => simp [finiteCosineProduct, sincTail]
  | succ n ih =>
      have hscale : sincTail n t =
          Complex.cos ((t : ℂ) / (2 : ℂ) ^ (n + 2)) * sincTail (n + 1) t := by
        unfold sincTail
        rw [complexSinc_eq_cos_mul]
        congr 1 <;> rw [pow_succ] <;> ring
      have hprod :
          (∏ k ∈ range (n + 1), complexSinc ((t : ℂ) / (2 : ℂ) ^ (k + 1))) =
            (∏ k ∈ range n, complexSinc ((t : ℂ) / (2 : ℂ) ^ (k + 1))) *
              sincTail n t := by
        simp [prod_range_succ, sincTail]
      rw [finiteCosineProduct_succ, hprod]
      rw [pow_succ]
      rw [← ih, hscale]
      ring

/-- The residual sinc factor in the telescoping identity tends to one even
after it is raised to the growing power `n`. -/
theorem tendsto_sincTail_pow (t : ℝ) :
    Tendsto (fun n : ℕ => sincTail n t ^ n) atTop (𝓝 1) := by
  have harg : Tendsto (fun n : ℕ => (t : ℂ) / (2 : ℂ) ^ (n + 1)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ => ((2 : ℂ)⁻¹) ^ (n + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)).comp
        (tendsto_add_atTop_nat 1)
    simpa [div_eq_mul_inv] using hpow.const_mul (t : ℂ)
  have hO : (fun n : ℕ => sincTail n t - 1) =O[atTop]
      (fun n : ℕ => (t : ℂ) / (2 : ℂ) ^ (n + 1)) := by
    exact complexSinc_sub_one_isBigO.comp_tendsto harg
  have hreal : Tendsto (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_abs_lt_one (by norm_num)
  have hcomplex : Tendsto
      (fun n : ℕ => (n : ℂ) * (1 / 2 : ℂ) ^ n) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hcomplexInv : Tendsto
      (fun n : ℕ => (n : ℂ) * ((2 : ℂ)⁻¹) ^ n) atTop (𝓝 0) := by
    simpa only [show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by simp [div_eq_mul_inv]] using hcomplex
  have hscaled := hcomplexInv.const_mul ((t : ℂ) / 2)
  have hargScaled : Tendsto
      (fun n : ℕ => (n : ℂ) * ((t : ℂ) / (2 : ℂ) ^ (n + 1))) atTop (𝓝 0) := by
    convert hscaled using 1
    · funext n
      rw [pow_succ]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    · ring
  have hnO : (fun n : ℕ => (n : ℂ)) =O[atTop] (fun n : ℕ => (n : ℂ)) :=
    isBigO_refl _ _
  have hsmall : Tendsto (fun n : ℕ => (n : ℂ) * (sincTail n t - 1)) atTop (𝓝 0) :=
    (hnO.mul hO).trans_tendsto hargScaled
  have hpow := Complex.tendsto_one_add_pow_exp_of_tendsto hsmall
  simpa using hpow

/-- The infinite sinc product written in the normalization naturally produced
by the characteristic functions of the convolution approximants. -/
noncomputable def shiftedSincProduct (t : ℝ) : ℂ :=
  ∏' k : ℕ, complexSinc ((t : ℂ) / (2 : ℂ) ^ (k + 1))

/-- The shifted sinc factors form a convergent infinite product. -/
lemma shiftedSincFactors_multipliable (t : ℝ) :
    Multipliable (fun k : ℕ => complexSinc ((t : ℂ) / (2 : ℂ) ^ (k + 1))) := by
  have h := sincFactors_multipliable ((t : ℂ) / (2 * Real.pi))
  convert h using 1
  funext k
  congr 1
  field_simp [Real.pi_ne_zero]
  rw [pow_succ]
  ring

/-- Conversion from the characteristic-function normalization to the paper's
Fourier-transform normalization. -/
lemma shiftedSincProduct_eq_rvachevFourierProduct (t : ℝ) :
    shiftedSincProduct t = rvachevFourierProduct (-(t : ℂ) / (2 * Real.pi)) := by
  unfold shiftedSincProduct rvachevFourierProduct
  apply tprod_congr
  intro k
  have harg : (Real.pi : ℂ) * (-(t : ℂ) / (2 * Real.pi)) / (2 : ℂ) ^ k =
      -((t : ℂ) / (2 : ℂ) ^ (k + 1)) := by
    field_simp [Real.pi_ne_zero]
    rw [pow_succ]
    ring
  rw [harg, complexSinc_neg]

/-- The partial shifted sinc products converge to `shiftedSincProduct`. -/
lemma tendsto_finiteSincProduct (t : ℝ) :
    Tendsto
      (fun n : ℕ => ∏ k ∈ range n,
        complexSinc ((t : ℂ) / (2 : ℂ) ^ (k + 1)))
      atTop (𝓝 (shiftedSincProduct t)) := by
  exact (shiftedSincFactors_multipliable t).tendsto_prod_tprod_nat

/-- The finite cosine products converge to the infinite sinc product. -/
theorem tendsto_finiteCosineProduct (t : ℝ) :
    Tendsto (fun n : ℕ => finiteCosineProduct n t) atTop
      (𝓝 (shiftedSincProduct t)) := by
  have hprod := tendsto_finiteSincProduct t
  have htail := tendsto_sincTail_pow t
  have hmul : Tendsto
      (fun n : ℕ => finiteCosineProduct n t * sincTail n t ^ n) atTop
      (𝓝 (shiftedSincProduct t)) := by
    exact hprod.congr' (Eventually.of_forall fun n =>
      (finiteCosineProduct_mul_sincTail_pow n t).symm)
  have hdiv := hmul.div htail one_ne_zero
  have hne : ∀ᶠ n : ℕ in atTop, sincTail n t ^ n ≠ 0 :=
    htail.eventually_ne one_ne_zero
  have heq : (fun n : ℕ =>
      (finiteCosineProduct n t * sincTail n t ^ n) / (sincTail n t ^ n)) =ᶠ[atTop]
      (fun n : ℕ => finiteCosineProduct n t) := by
    filter_upwards [hne] with n hn
    field_simp
  simpa using hdiv.congr' heq

/-- The characteristic function of the `n`th finite convolution is its
finite weighted cosine product. -/
theorem finiteConvolutionMeasure_charFun_eq_finiteCosineProduct (n : ℕ) (t : ℝ) :
    charFun (finiteConvolutionMeasure n) t = finiteCosineProduct n t := by
  rw [finiteConvolutionMeasure_charFun]
  unfold finiteCosineProduct
  apply prod_congr rfl
  intro k hk
  congr 1
  rw [Complex.ofReal_cos]
  congr 1
  push_cast
  norm_cast

/-- Pointwise convergence of the characteristic functions in Lemma 1. -/
theorem finiteConvolutionMeasure_charFun_tendsto
    (F : BoundedFabius) (hF : IsFabius F) (t : ℝ) :
    Tendsto (fun n : ℕ => charFun (finiteConvolutionMeasure n) t) atTop
      (𝓝 (charFun (rvachevMeasure F) t)) := by
  have h := tendsto_finiteCosineProduct t
  rw [shiftedSincProduct_eq_rvachevFourierProduct,
    ← rvachevFourier_eq_product F hF,
    ← rvachevMeasure_charFun F hF] at h
  exact h.congr' (Eventually.of_forall fun n =>
    (finiteConvolutionMeasure_charFun_eq_finiteCosineProduct n t).symm)

/-- The finite convolution measures, bundled as probability measures. -/
noncomputable def finiteConvolutionProbability (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨finiteConvolutionMeasure n, inferInstance⟩

/-- The measure with density Rvachev's up function, bundled as a probability measure. -/
noncomputable def rvachevProbability (F : BoundedFabius) (hF : IsFabius F) :
    ProbabilityMeasure ℝ :=
  ⟨rvachevMeasure F, rvachevMeasure_isProbability F hF⟩

/-- Lemma 1: the finite convolutions converge weakly to the measure with
density Rvachev's up function. -/
theorem finiteConvolutionProbability_tendsto
    (F : BoundedFabius) (hF : IsFabius F) :
    Tendsto finiteConvolutionProbability atTop (𝓝 (rvachevProbability F hF)) := by
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  simpa [finiteConvolutionProbability, rvachevProbability] using
    finiteConvolutionMeasure_charFun_tendsto F hF t

/-- Weak convergence tested against bounded continuous functions valued in
any real-or-complex-like field. -/
theorem integral_finiteConvolutionMeasure_rclike_tendsto
    (𝕜 : Type*) [RCLike 𝕜]
    (F : BoundedFabius) (hF : IsFabius F) (g : ℝ →ᵇ 𝕜) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, g x ∂finiteConvolutionMeasure n) atTop
      (nhds (∫ x : ℝ, g x ∂rvachevMeasure F)) := by
  have h := finiteConvolutionProbability_tendsto F hF
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜] at h
  simpa [finiteConvolutionProbability, rvachevProbability] using h g

/-- The real bounded-continuous-test-function formulation of Lemma 1. -/
theorem integral_finiteConvolutionMeasure_tendsto
    (F : BoundedFabius) (hF : IsFabius F) (g : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, g x ∂finiteConvolutionMeasure n) atTop
      (𝓝 (∫ x : ℝ, g x ∂rvachevMeasure F)) :=
  integral_finiteConvolutionMeasure_rclike_tendsto ℝ F hF g

/-- The complex bounded-continuous-test-function formulation used literally
by the paper's complex Banach space of test functions. -/
theorem integral_finiteConvolutionMeasure_complex_tendsto
    (F : BoundedFabius) (hF : IsFabius F) (g : ℝ →ᵇ ℂ) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, g x ∂finiteConvolutionMeasure n) atTop
      (𝓝 (∫ x : ℝ, g x ∂rvachevMeasure F)) :=
  integral_finiteConvolutionMeasure_rclike_tendsto ℂ F hF g

/-- Lemma 1 specialized to the canonical Fabius function. -/
theorem finiteConvolutionProbability_tendsto_fabius :
    Tendsto finiteConvolutionProbability atTop
      (𝓝 (rvachevProbability fabius fabius_spec)) :=
  finiteConvolutionProbability_tendsto fabius fabius_spec

/-- The canonical Fabius specialization against a bounded continuous test function. -/
theorem integral_finiteConvolutionMeasure_tendsto_fabius (g : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, g x ∂finiteConvolutionMeasure n) atTop
      (𝓝 (∫ x : ℝ, g x ∂rvachevMeasure fabius)) :=
  integral_finiteConvolutionMeasure_tendsto fabius fabius_spec g

/-- The canonical Fabius specialization for any `RCLike`-valued bounded
continuous test function. -/
theorem integral_finiteConvolutionMeasure_rclike_tendsto_fabius
    (𝕜 : Type*) [RCLike 𝕜] (g : ℝ →ᵇ 𝕜) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, g x ∂finiteConvolutionMeasure n) atTop
      (nhds (∫ x : ℝ, g x ∂rvachevMeasure fabius)) :=
  integral_finiteConvolutionMeasure_rclike_tendsto 𝕜 fabius fabius_spec g

/-- The canonical complex-valued bounded-test-function specialization. -/
theorem integral_finiteConvolutionMeasure_complex_tendsto_fabius (g : ℝ →ᵇ ℂ) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, g x ∂finiteConvolutionMeasure n) atTop
      (𝓝 (∫ x : ℝ, g x ∂rvachevMeasure fabius)) :=
  integral_finiteConvolutionMeasure_rclike_tendsto_fabius ℂ g

end

end Fabius

import FabiusFunction.MeasureRefinement
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Geometrically self-similar cumulant tails

The fourth face of the Thue–Morse volume's *reusable geometric-tail
API* obligation: the "tail equals a scaled copy of the whole" identity
for cumulant generating functions.  The product face is
`GeometricScaleProducts.lean`, the convolution face is
`GeometricConvolutionTails.lean`, the random-series face is the
splitting of `RandomSeriesLaw.lean`; this module turns the convolution
face's structure theorems into moment- and cumulant-generating
identities.

The moment layer is unconditional: with `mgf` taken at the identity
(so `mgf id μ` is the moment generating function of the *measure*),

* `mgf_id_conv` — `mgf` of a convolution is the product of the `mgf`s
  (no integrability hypotheses: the product-measure factorization
  `integral_prod_mul` handles the junk cases coherently);
* `mgf_id_mulPrefix` — the prefix system's `mgf` is the finite product
  `∏_{k<m} M_ν(c^k t)`;
* `mgf_id_self_similar` — from the one-step refinement,
  `M_μ(t) = ∏_{k<m} M_ν(c^k t) · M_μ(c^m t)` for every `m`.

The cumulant layer takes logarithms, so it carries the honest
finite-exponential-moment hypotheses:

* `cgf_id_mulPrefix` — `K_{P_m}(t) = ∑_{k<m} K_ν(c^k t)`;
* `cgf_id_self_similar` — **the cumulant tail law**
  `K_μ(t) = ∑_{k<m} K_ν(c^k t) + K_μ(c^m t)`.

The dyadic instance closes the circle with no hypotheses left: the
uniform digit and the up-measure are compactly supported, so every
exponential moment is finite (`integrable_exp_uniform_half`,
`integrable_exp_rvachevMeasure`), and

* `cgf_uniformDigitPrefix` — the digit prefix's cumulants split;
* `cgf_rvachevMeasure_self_similar` — the up-measure's cumulant
  generating function satisfies the geometric tail law
  `K(t) = ∑_{k<m} K_U(2^{-k} t) + K(2^{-m} t)` — the volume's
  cumulant-operator identity, derived from the refinement equation
  through the abstract API.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real Set

namespace Fabius

section MomentLayer

variable {μ ν : Measure ℝ}

/-- **The moment generating function of a convolution** is the product
of the moment generating functions — unconditionally: both sides
degrade coherently when an exponential moment is infinite, through the
unconditional product-measure factorization. -/
theorem mgf_id_conv [SFinite μ] [SFinite ν] (t : ℝ) :
    mgf id (μ ∗ ν) t = mgf id μ t * mgf id ν t := by
  simp only [mgf, id_eq]
  unfold Measure.conv
  rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  calc ∫ p : ℝ × ℝ, exp (t * (p.1 + p.2)) ∂(μ.prod ν)
      = ∫ p : ℝ × ℝ, exp (t * p.1) * exp (t * p.2) ∂(μ.prod ν) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        show Real.exp (t * (p.1 + p.2)) =
          Real.exp (t * p.1) * Real.exp (t * p.2)
        rw [mul_add, Real.exp_add]
    _ = (∫ x, exp (t * x) ∂μ) * ∫ y, exp (t * y) ∂ν :=
        integral_prod_mul (fun x => exp (t * x)) fun y => exp (t * y)

/-- The moment generating function of a scaled pushforward rescales
the argument. -/
theorem mgf_id_map_const_mul (μ : Measure ℝ) (c t : ℝ) :
    mgf id (μ.map (c * ·)) t = mgf id μ (c * t) := by
  rw [mgf_id_map (measurable_const_mul c).aemeasurable]
  exact mgf_const_mul c

/-- **The moment generating function of the prefix system** is the
finite product of rescaled digit moment generating functions. -/
theorem mgf_id_mulPrefix (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (c : ℝ) (m : ℕ) (t : ℝ) :
    mgf id (mulPrefix ν c m) t =
      ∏ k ∈ Finset.range m, mgf id ν (c ^ k * t) := by
  induction m generalizing t with
  | zero => simp [mgf]
  | succ m ih =>
      haveI := isProbabilityMeasure_mulPrefix (ν := ν) c m
      haveI : IsProbabilityMeasure ((mulPrefix ν c m).map (c * ·)) :=
        Measure.isProbabilityMeasure_map
          (measurable_const_mul c).aemeasurable
      rw [mulPrefix_succ, mgf_id_conv, mgf_id_map_const_mul, ih,
        Finset.prod_range_succ', pow_zero, one_mul, mul_comm]
      congr 1
      exact Finset.prod_congr rfl fun k _ => by
        rw [← mul_assoc, ← pow_succ]

/-- **The moment tail law**: from the one-step refinement
`μ = ν ∗ (c·)_* μ`, the moment generating function factors through
every scale, `M_μ(t) = ∏_{k<m} M_ν(c^k t) · M_μ(c^m t)`. -/
theorem mgf_id_self_similar {c : ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : μ = ν ∗ μ.map (c * ·)) (m : ℕ)
    (t : ℝ) :
    mgf id μ t =
      (∏ k ∈ Finset.range m, mgf id ν (c ^ k * t)) *
        mgf id μ (c ^ m * t) := by
  haveI := isProbabilityMeasure_mulPrefix (ν := ν) c m
  haveI : IsProbabilityMeasure (μ.map (c ^ m * ·)) :=
    Measure.isProbabilityMeasure_map
      (measurable_const_mul _).aemeasurable
  conv_lhs => rw [self_similar_conv_iterate_mul h m]
  rw [mgf_id_conv, mgf_id_mulPrefix, mgf_id_map_const_mul]

end MomentLayer

section CumulantLayer

variable {μ ν : Measure ℝ}

/-- **The cumulant generating function of the prefix system** is the
finite sum of rescaled digit cumulants, under finite exponential
moments of the digit at each scale. -/
theorem cgf_id_mulPrefix (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (c : ℝ) (m : ℕ) (t : ℝ)
    (hint : ∀ k, Integrable (fun x => exp ((c ^ k * t) * x)) ν) :
    cgf id (mulPrefix ν c m) t =
      ∑ k ∈ Finset.range m, cgf id ν (c ^ k * t) := by
  simp only [cgf]
  rw [mgf_id_mulPrefix]
  exact Real.log_prod fun k _ => (mgf_pos (X := id) (hint k)).ne'

/-- **The cumulant tail law**: from the one-step refinement, the
cumulant generating function splits off `m` geometric digit layers,
`K_μ(t) = ∑_{k<m} K_ν(c^k t) + K_μ(c^m t)`. -/
theorem cgf_id_self_similar {c : ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : μ = ν ∗ μ.map (c * ·)) (m : ℕ)
    (t : ℝ)
    (hν : ∀ k, Integrable (fun x => exp ((c ^ k * t) * x)) ν)
    (hμ : Integrable (fun x => exp ((c ^ m * t) * x)) μ) :
    cgf id μ t =
      (∑ k ∈ Finset.range m, cgf id ν (c ^ k * t)) +
        cgf id μ (c ^ m * t) := by
  simp only [cgf]
  rw [mgf_id_self_similar h m t,
    Real.log_mul
      (Finset.prod_ne_zero_iff.mpr fun k _ =>
        (mgf_pos (X := id) (hν k)).ne')
      (mgf_pos (X := id) hμ).ne']
  congr 1
  exact Real.log_prod fun k _ => (mgf_pos (X := id) (hν k)).ne'

end CumulantLayer

section DyadicInstance

/-- Every exponential moment of the unit uniform digit is finite. -/
theorem integrable_exp_uniform_half (s : ℝ) :
    Integrable (fun x => exp (s * x))
      (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) :=
  (Continuous.continuousOn (by fun_prop)).integrableOn_compact
    isCompact_Icc

/-- **The dyadic digit prefix's cumulants split exactly**:
`K_{P_m}(t) = ∑_{k<m} K_U(2^{-k} t)` for the uniform digit `U`, with
no hypotheses — all exponential moments are finite by compact
support. -/
theorem cgf_uniformDigitPrefix (m : ℕ) (t : ℝ) :
    cgf id (uniformDigitPrefix m) t =
      ∑ k ∈ Finset.range m,
        cgf id (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹))
          ((2⁻¹ : ℝ) ^ k * t) := by
  haveI := isProbability_uniform_half
  rw [uniformDigitPrefix_eq_mulPrefix]
  exact cgf_id_mulPrefix _ _ m t fun k => integrable_exp_uniform_half _

/-- Every exponential moment of the up-measure is finite: the density
is bounded by one and supported in `[-1,1]`. -/
theorem integrable_exp_rvachevMeasure (F : BoundedFabius)
    (hF : IsFabius F) (s : ℝ) :
    Integrable (fun x => exp (s * x)) (rvachevMeasure F) := by
  rw [rvachevMeasure, integrable_withDensity_iff
    ((rvachev_contDiff F hF).continuous.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have hshape : (fun x => exp (s * x) * (ENNReal.ofReal
      (rvachevUp F x)).toReal) = fun x => exp (s * x) * rvachevUp F x :=
    funext fun x => by rw [ENNReal.toReal_ofReal (rvachevUp_nonneg F x)]
  rw [hshape]
  refine Integrable.mono' ((rvachevUp_integrable F hF).const_mul
    (exp |s|))
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (rvachev_contDiff F hF).continuous).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rvachevUp_nonneg F x),
    abs_of_pos (Real.exp_pos _)]
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · refine mul_le_mul_of_nonneg_right ?_ (rvachevUp_nonneg F x)
    refine Real.exp_le_exp.mpr ?_
    calc s * x ≤ |s * x| := le_abs_self _
      _ = |s| * |x| := abs_mul s x
      _ ≤ |s| * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)
          rw [abs_le]
          constructor <;> [linarith [hx.1]; linarith [hx.2]]
      _ = |s| := mul_one _
  · rw [rvachevUp_eq_zero_of_not_mem_Ioo F hF hx, mul_zero, mul_zero]

/-- **The up-measure's cumulant tail law, fully instantiated**: the
cumulant generating function of the up-measure splits off any number
of uniform digit layers,
`K(t) = ∑_{k<m} K_U(2^{-k} t) + K(2^{-m} t)` — the volume's
cumulant-operator identity, with every hypothesis discharged by
compact support. -/
theorem cgf_rvachevMeasure_self_similar (F : BoundedFabius)
    (hF : IsFabius F) (m : ℕ) (t : ℝ) :
    cgf id (rvachevMeasure F) t =
      (∑ k ∈ Finset.range m,
        cgf id (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹))
          ((2⁻¹ : ℝ) ^ k * t)) +
        cgf id (rvachevMeasure F) ((2⁻¹ : ℝ) ^ m * t) := by
  haveI := rvachevMeasure_isProbability F hF
  haveI := isProbability_uniform_half
  exact cgf_id_self_similar (rvachevMeasure_refinement F hF) m t
    (fun k => integrable_exp_uniform_half _)
    (integrable_exp_rvachevMeasure F hF _)

end DyadicInstance

section UniformClosedForm

/-- **The closed moment generating function of the uniform digit**:
`M_U(t) = 2·sinh(t/2)/t` for `t ≠ 0` — the real-argument counterpart
of the digit's characteristic function `sinc(t/2)`. -/
theorem mgf_uniform_half (t : ℝ) (ht : t ≠ 0) :
    mgf id (MeasureTheory.volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) t =
      2 * Real.sinh (t / 2) / t := by
  simp only [mgf, id_eq]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le
      (by norm_num : -(2⁻¹ : ℝ) ≤ 2⁻¹),
    intervalIntegral.integral_comp_mul_left (f := Real.exp) ht,
    integral_exp, smul_eq_mul, Real.sinh_eq]
  have h1 : t * 2⁻¹ = t / 2 := by ring
  have h2 : t * -2⁻¹ = -(t / 2) := by ring
  rw [h1, h2]
  field_simp
  ring

/-- The digit prefix's moment generating function in closed form: the
finite hyperbolic-sinc product
`M_{P_m}(t) = ∏_{k<m} 2·sinh(2^{-k}t/2)/(2^{-k}t)`. -/
theorem mgf_uniformDigitPrefix (m : ℕ) (t : ℝ) (ht : t ≠ 0) :
    mgf id (uniformDigitPrefix m) t =
      ∏ k ∈ Finset.range m,
        2 * Real.sinh ((2⁻¹ : ℝ) ^ k * t / 2) / ((2⁻¹ : ℝ) ^ k * t) := by
  haveI := isProbability_uniform_half
  rw [uniformDigitPrefix_eq_mulPrefix, mgf_id_mulPrefix]
  exact Finset.prod_congr rfl fun k _ =>
    mgf_uniform_half _ (mul_ne_zero (by positivity) ht)

end UniformClosedForm

end Fabius

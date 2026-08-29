import FabiusFunction.StieltjesMomentLaurent
import FabiusFunction.CauchyTransform

/-!
# The complex Cauchy transform of the up-measure

The complex-`z` face of the moment/Laurent layer: for every complex
`z` with `‖z‖ > 1` the Cauchy transform of the up-measure expands in
the real moments,

`∫ (z-x)⁻¹ dμ_up = ∑_{k<N} m_k·z^{-(k+1)} + z^{-N}·∫ x^N/(z-x) dμ_up`,

with the geometric remainder bound `(‖z‖-1)⁻¹·‖z‖^{-N}`, hence the
convergent Laurent series `∫ (z-x)⁻¹ dμ_up = ∑'_k m_k·z^{-(k+1)}` on
the exterior of the unit disc — the analytic germ from which the
Stieltjes inversion and boundary theory of the transform layer
proceed.  The kernel identity is inherited from the field-general
`inv_sub_eq_sum_range_add`; the moments are the same Hankel data as
in the real program.
-/

set_option autoImplicit false

open MeasureTheory

namespace Fabius

/-- Off the closed unit disc the complex Cauchy kernel is integrable:
it is bounded by `(‖z‖-1)⁻¹` almost everywhere. -/
theorem integrable_inv_sub_complex_rvachevMeasure (F : BoundedFabius)
    (hF : IsFabius F) {z : ℂ} (hz : 1 < ‖z‖) :
    Integrable (fun x : ℝ => (z - x)⁻¹) (rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  refine Integrable.mono' (integrable_const ((‖z‖ - 1)⁻¹))
    ((measurable_const.sub Complex.continuous_ofReal.measurable).inv
      .aestronglyMeasurable) ?_
  filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
  have hxabs : ‖(x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩)
  have hle : ‖z‖ - 1 ≤ ‖z - x‖ := by
    have h := norm_sub_norm_le z ((x : ℝ) : ℂ)
    linarith
  rw [norm_inv, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by linarith) hle

/-- The complex remainder kernel is likewise integrable. -/
theorem integrable_pow_div_sub_complex_rvachevMeasure
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ} (hz : 1 < ‖z‖)
    (N : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ N / (z - x))
      (rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  refine Integrable.mono' (integrable_const ((‖z‖ - 1)⁻¹))
    (((Complex.continuous_ofReal.measurable.pow_const N).div
      (measurable_const.sub Complex.continuous_ofReal.measurable))
      .aestronglyMeasurable) ?_
  filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
  have hxabs : ‖(x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩)
  have hle : ‖z‖ - 1 ≤ ‖z - x‖ := by
    have h := norm_sub_norm_le z ((x : ℝ) : ℂ)
    linarith
  have hpow : ‖(x : ℂ) ^ N‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hxabs
  rw [norm_div, inv_eq_one_div]
  exact div_le_div₀ (by norm_num) hpow (by linarith) hle

/-- **The complex moment/Laurent expansion with exact remainder**:
`∫ (z-x)⁻¹ dμ_up = ∑_{k<N} m_k/z^{k+1} + z^{-N}·∫ x^N/(z-x) dμ_up`
for `‖z‖ > 1`. -/
theorem integral_inv_sub_complex_eq_sum_upMoment_add
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ} (hz : 1 < ‖z‖)
    (N : ℕ) :
    ∫ x, (z - x)⁻¹ ∂(rvachevMeasure F) =
      (∑ k ∈ Finset.range N, (upMoment F k : ℂ) / z ^ (k + 1)) +
        (z ^ N)⁻¹ *
          ∫ x, (x : ℂ) ^ N / (z - x) ∂(rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  have hzne : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz
    linarith
  have hintpow0 : ∀ k : ℕ, Integrable
      (fun x : ℝ => (x : ℂ) ^ k) (rvachevMeasure F) := by
    intro k
    refine Integrable.mono' (integrable_const 1)
      ((Complex.continuous_ofReal.measurable.pow_const
        k).aestronglyMeasurable) ?_
    filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_one₀ (abs_nonneg x)
      (le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩))
  have hintpowC : ∀ k : ℕ, Integrable
      (fun x : ℝ => ((x : ℂ) ^ k / z ^ (k + 1))) (rvachevMeasure F) := by
    intro k
    have h := (hintpow0 k).const_mul ((z ^ (k + 1))⁻¹)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [division_def, mul_comm]
  have hintrem : Integrable
      (fun x : ℝ => (x : ℂ) ^ N / (z ^ N * (z - x)))
      (rvachevMeasure F) := by
    have h := (integrable_pow_div_sub_complex_rvachevMeasure F hF hz
      N).const_mul ((z ^ N)⁻¹)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [division_def, division_def, mul_inv]
    ring
  calc ∫ x, (z - x)⁻¹ ∂(rvachevMeasure F)
      = ∫ x, ((∑ k ∈ Finset.range N, (x : ℂ) ^ k / z ^ (k + 1)) +
          (x : ℂ) ^ N / (z ^ N * (z - x))) ∂(rvachevMeasure F) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
        have hxlt : ‖((x : ℝ) : ℂ)‖ < 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact abs_lt.mpr ⟨hx.1, hx.2⟩
        have hzx : z - x ≠ 0 := by
          refine norm_pos_iff.mp ?_
          have h := norm_sub_norm_le z ((x : ℝ) : ℂ)
          linarith
        exact inv_sub_eq_sum_range_add N hzne hzx
    _ = (∑ k ∈ Finset.range N,
          ∫ x, (x : ℂ) ^ k / z ^ (k + 1) ∂(rvachevMeasure F)) +
        ∫ x, (x : ℂ) ^ N / (z ^ N * (z - x)) ∂(rvachevMeasure F) := by
        rw [integral_add (integrable_finsetSum _ fun k _ => hintpowC k)
          hintrem, integral_finsetSum _ fun k _ => hintpowC k]
    _ = (∑ k ∈ Finset.range N, (upMoment F k : ℂ) / z ^ (k + 1)) +
        (z ^ N)⁻¹ *
          ∫ x, (x : ℂ) ^ N / (z - x) ∂(rvachevMeasure F) := by
        congr 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          have hfun : (fun x : ℝ => (x : ℂ) ^ k / z ^ (k + 1)) =
              fun x : ℝ => (z ^ (k + 1))⁻¹ * ((x ^ k : ℝ) : ℂ) := by
            funext x
            rw [Complex.ofReal_pow, division_def, mul_comm]
          rw [hfun, MeasureTheory.integral_const_mul,
            integral_complex_ofReal, upMoment, division_def, mul_comm]
        · have hfun : (fun x : ℝ =>
              (x : ℂ) ^ N / (z ^ N * (z - x))) =
              fun x : ℝ => (z ^ N)⁻¹ * ((x : ℂ) ^ N / (z - x)) := by
            funext x
            rw [division_def, division_def, mul_inv]
            ring
          rw [hfun, MeasureTheory.integral_const_mul]

/-- **The geometric tail bound for the complex transform**: the
Laurent remainder decays like `(‖z‖-1)⁻¹·‖z‖^{-N}`. -/
theorem norm_integral_inv_sub_complex_sub_sum_le (F : BoundedFabius)
    (hF : IsFabius F) {z : ℂ} (hz : 1 < ‖z‖) (N : ℕ) :
    ‖(∫ x, (z - x)⁻¹ ∂(rvachevMeasure F)) -
        ∑ k ∈ Finset.range N, (upMoment F k : ℂ) / z ^ (k + 1)‖ ≤
      (‖z‖ - 1)⁻¹ / ‖z‖ ^ N := by
  haveI := rvachevMeasure_isProbability F hF
  have hrem : (∫ x, (z - x)⁻¹ ∂(rvachevMeasure F)) -
      ∑ k ∈ Finset.range N, (upMoment F k : ℂ) / z ^ (k + 1) =
      (z ^ N)⁻¹ *
        ∫ x, (x : ℂ) ^ N / (z - x) ∂(rvachevMeasure F) := by
    rw [integral_inv_sub_complex_eq_sum_upMoment_add F hF hz N]
    ring
  rw [hrem, norm_mul, norm_inv, norm_pow]
  have hbound : ‖∫ x, (x : ℂ) ^ N / (z - x) ∂(rvachevMeasure F)‖ ≤
      (‖z‖ - 1)⁻¹ := by
    have h := norm_integral_le_of_norm_le_const
      (μ := rvachevMeasure F)
      (f := fun x : ℝ => (x : ℂ) ^ N / (z - x))
      (C := (‖z‖ - 1)⁻¹) ?_
    · simpa using h
    filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
    have hxabs : ‖(x : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩)
    have hle : ‖z‖ - 1 ≤ ‖z - x‖ := by
      have h := norm_sub_norm_le z ((x : ℝ) : ℂ)
      linarith
    have hpow : ‖(x : ℂ) ^ N‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hxabs
    rw [norm_div, inv_eq_one_div]
    exact div_le_div₀ (by norm_num) hpow (by linarith) hle
  calc (‖z‖ ^ N)⁻¹ * ‖∫ x, (x : ℂ) ^ N / (z - x) ∂(rvachevMeasure F)‖
      ≤ (‖z‖ ^ N)⁻¹ * (‖z‖ - 1)⁻¹ := by
        refine mul_le_mul_of_nonneg_left hbound ?_
        positivity
    _ = (‖z‖ - 1)⁻¹ / ‖z‖ ^ N := by
        rw [division_def]
        ring

/-- The complex Laurent series is summable: geometric comparison. -/
theorem summable_upMoment_laurent_complex (F : BoundedFabius)
    (hF : IsFabius F) {z : ℂ} (hz : 1 < ‖z‖) :
    Summable (fun k : ℕ => (upMoment F k : ℂ) / z ^ (k + 1)) := by
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  refine Summable.of_norm_bounded
    (g := fun k : ℕ => ‖z‖⁻¹ ^ k * ‖z‖⁻¹)
    ((summable_geometric_of_lt_one (by positivity)
      ((inv_lt_one₀ hzpos).mpr hz)).mul_right _) fun k => ?_
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc |upMoment F k| / ‖z‖ ^ (k + 1) ≤ 1 / ‖z‖ ^ (k + 1) :=
        div_le_div₀ (by norm_num) (abs_upMoment_le_one F hF k)
          (by positivity) le_rfl
    _ = ‖z‖⁻¹ ^ k * ‖z‖⁻¹ := by
        rw [one_div, pow_succ, mul_inv, ← inv_pow]

/-- **The convergent complex Laurent series**: on the exterior of the
unit disc, `∫ (z-x)⁻¹ dμ_up = ∑'_k m_k·z^{-(k+1)}`. -/
theorem integral_inv_sub_complex_eq_tsum_upMoment (F : BoundedFabius)
    (hF : IsFabius F) {z : ℂ} (hz : 1 < ‖z‖) :
    ∫ x, (z - x)⁻¹ ∂(rvachevMeasure F) =
      ∑' k : ℕ, (upMoment F k : ℂ) / z ^ (k + 1) := by
  have hsum := summable_upMoment_laurent_complex F hF hz
  have htend1 : Filter.Tendsto
      (fun N => ∑ k ∈ Finset.range N,
        (upMoment F k : ℂ) / z ^ (k + 1))
      Filter.atTop
      (nhds (∑' k : ℕ, (upMoment F k : ℂ) / z ^ (k + 1))) :=
    hsum.hasSum.tendsto_sum_nat
  have hg : Filter.Tendsto (fun N : ℕ => (‖z‖ - 1)⁻¹ / ‖z‖ ^ N)
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun N : ℕ => (‖z‖⁻¹) ^ N)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        ((inv_lt_one₀ (by linarith)).mpr hz)
    have h1 := h0.const_mul ((‖z‖ - 1)⁻¹)
    rw [mul_zero] at h1
    refine h1.congr fun N => ?_
    rw [inv_pow, division_def]
  have htend2 : Filter.Tendsto
      (fun N => ∑ k ∈ Finset.range N,
        (upMoment F k : ℂ) / z ^ (k + 1))
      Filter.atTop
      (nhds (∫ x, (z - x)⁻¹ ∂(rvachevMeasure F))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun N => dist_nonneg) (fun N => ?_) hg
    rw [dist_eq_norm, norm_sub_rev]
    exact norm_integral_inv_sub_complex_sub_sum_le F hF hz N
  exact tendsto_nhds_unique htend2 htend1

/-- `HasSum` form of the convergent complex Laurent expansion. -/
theorem hasSum_upMoment_laurent_complex (F : BoundedFabius)
    (hF : IsFabius F) {z : ℂ} (hz : 1 < ‖z‖) :
    HasSum (fun k : ℕ => (upMoment F k : ℂ) / z ^ (k + 1))
      (∫ x, (z - x)⁻¹ ∂(rvachevMeasure F)) := by
  rw [integral_inv_sub_complex_eq_tsum_upMoment F hF hz]
  exact (summable_upMoment_laurent_complex F hF hz).hasSum

/-- **The real transform is the restriction of the complex one**: on
the real exterior the two Laurent programs agree,
`∫ (z-x)⁻¹_ℂ dμ_up = ↑(∫ (z-x)⁻¹_ℝ dμ_up)`. -/
theorem integral_inv_sub_complex_ofReal (F : BoundedFabius)
    (hF : IsFabius F) {z : ℝ} (hz : 1 < |z|) :
    ∫ x, (((z : ℝ) : ℂ) - x)⁻¹ ∂(rvachevMeasure F) =
      ((∫ x, (z - x)⁻¹ ∂(rvachevMeasure F) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  rw [Complex.ofReal_inv, Complex.ofReal_sub]

/-- **The Laurent expansion of the named Cauchy transform**: on the
exterior of the unit disc the corpus's `rvachevCauchyTransform` is
the convergent moment series `∑'_k m_k·z^{-(k+1)}`. -/
theorem rvachevCauchyTransform_eq_tsum_upMoment (F : BoundedFabius)
    (hF : IsFabius F) {z : ℂ} (hz : 1 < ‖z‖) :
    rvachevCauchyTransform F z =
      ∑' k : ℕ, (upMoment F k : ℂ) / z ^ (k + 1) := by
  rw [rvachevCauchyTransform_apply]
  exact integral_inv_sub_complex_eq_tsum_upMoment F hF hz

end Fabius

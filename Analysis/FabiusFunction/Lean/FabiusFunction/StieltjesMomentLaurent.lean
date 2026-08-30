import FabiusFunction.MeasureCauchyMomentLaurent
import FabiusFunction.MomentHankelMatrix

/-!
# The moment/Laurent layer of the up-measure's Stieltjes transform

The transform-layer obligation's moment/Laurent item: outside the
support, the Stieltjes transform of the up-measure expands in the
moments with an *exact* remainder,

`∫ (z-x)⁻¹ dμ_up = ∑_{k<N} m_k·z^{-(k+1)} + z^{-N}·∫ x^N/(z-x) dμ_up`,

for every `N` and every real `z` with `|z| > 1`, and the remainder is
bounded by `(|z|-1)⁻¹·|z|^{-N}` — the Laurent series converges
geometrically.  The moments `m_k = upMoment F k` are exactly the
Hankel data of the orthogonal-polynomial layer, so this is the
analytic face of the J-fraction: the same numbers drive the
determinant polynomials and the asymptotic expansion of the
transform.

* `inv_sub_eq_sum_range_add` — the finite geometric expansion of the
  Cauchy kernel, inherited from the generic measure-level Laurent layer;
* `integrable_inv_sub_rvachevMeasure` — integrability of the kernel
  off the support;
* `integral_inv_sub_eq_sum_upMoment_add` — the expansion with exact
  remainder;
* `abs_integral_inv_sub_sub_sum_le` — the geometric tail bound.
-/

set_option autoImplicit false

open MeasureTheory

namespace Fabius

/-- Almost every point of the up-measure lies in `(-1,1)`. -/
theorem ae_mem_Ioo_rvachevMeasure (F : BoundedFabius)
    (hF : IsFabius F) :
    ∀ᵐ x ∂(rvachevMeasure F), x ∈ Set.Ioo (-1 : ℝ) 1 := by
  haveI := rvachevMeasure_isProbability F hF
  have hcompl : rvachevMeasure F (Set.Ioo (-1 : ℝ) 1)ᶜ = 0 :=
    (prob_compl_eq_zero_iff measurableSet_Ioo).mpr
      (rvachevMeasure_Ioo_eq_one F hF)
  exact mem_ae_iff.mpr hcompl

/-- The up-measure lies almost everywhere in the unit ball after embedding
the real line into any real-or-complex scalar field. -/
theorem ae_norm_sub_zero_le_one_rvachevMeasure
    {𝕜 : Type*} [RCLike 𝕜]
    (F : BoundedFabius) (hF : IsFabius F) :
    ∀ᵐ x : ℝ ∂(rvachevMeasure F), ‖(x : 𝕜) - (0 : 𝕜)‖ ≤ 1 := by
  filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
  rw [sub_zero, RCLike.norm_ofReal]
  exact le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩)

/-- Centering the generic measure moment at zero recovers the up-measure
moment used by the Hankel and Jacobi layers, in any `RCLike` scalar field. -/
@[simp] theorem measureCauchyMoment_rvachevMeasure_zero
    {𝕜 : Type*} [RCLike 𝕜]
    (F : BoundedFabius) (n : ℕ) :
    measureCauchyMoment (𝕜 := 𝕜) (rvachevMeasure F) 0 n =
      (upMoment F n : 𝕜) := by
  rw [measureCauchyMoment, upMoment]
  calc
    (∫ x : ℝ, ((x : 𝕜) - 0) ^ n ∂(rvachevMeasure F)) =
        ∫ x : ℝ, ((x ^ n : ℝ) : 𝕜) ∂(rvachevMeasure F) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [sub_zero, RCLike.ofReal_pow]
    _ = ((∫ x : ℝ, x ^ n ∂(rvachevMeasure F) : ℝ) : 𝕜) := by
      exact integral_ofReal

/-- Off the support the Cauchy kernel is integrable: it is bounded by
`(|z|-1)⁻¹` almost everywhere. -/
theorem integrable_inv_sub_rvachevMeasure (F : BoundedFabius)
    (hF : IsFabius F) {z : ℝ} (hz : 1 < |z|) :
    Integrable (fun x => (z - x)⁻¹) (rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  have hball : ∀ᵐ x : ℝ ∂(rvachevMeasure F),
      ‖((x : ℝ) : ℝ) - (0 : ℝ)‖ ≤ 1 := by
    exact ae_norm_sub_zero_le_one_rvachevMeasure (𝕜 := ℝ) F hF
  have hz' : (1 : ℝ) < ‖((z : ℝ) : ℝ) - (0 : ℝ)‖ := by
    simpa only [sub_zero, Real.norm_eq_abs] using hz
  simpa using
    (integrable_inv_sub_of_ae_norm_sub_le
      (𝕜 := ℝ) (rvachevMeasure F) (c := 0) (R := 1)
      (by norm_num) hball hz')

/-- The remainder kernel is likewise integrable. -/
theorem integrable_pow_div_sub_rvachevMeasure (F : BoundedFabius)
    (hF : IsFabius F) {z : ℝ} (hz : 1 < |z|) (N : ℕ) :
    Integrable (fun x => x ^ N / (z - x)) (rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  have hball : ∀ᵐ x : ℝ ∂(rvachevMeasure F),
      ‖((x : ℝ) : ℝ) - (0 : ℝ)‖ ≤ 1 := by
    exact ae_norm_sub_zero_le_one_rvachevMeasure (𝕜 := ℝ) F hF
  have hz' : (1 : ℝ) < ‖((z : ℝ) : ℝ) - (0 : ℝ)‖ := by
    simpa only [sub_zero, Real.norm_eq_abs] using hz
  simpa using
    (integrable_centered_pow_div_sub_of_ae_norm_sub_le
      (𝕜 := ℝ) (rvachevMeasure F) (c := 0) (R := 1)
      (by norm_num) hball hz' N)

/-- **The finite moment/Laurent expansion with exact remainder**:
`∫ (z-x)⁻¹ dμ_up = ∑_{k<N} m_k/z^{k+1} + z^{-N}·∫ x^N/(z-x) dμ_up`
for `|z| > 1`. -/
theorem integral_inv_sub_eq_sum_upMoment_add (F : BoundedFabius)
    (hF : IsFabius F) {z : ℝ} (hz : 1 < |z|) (N : ℕ) :
    ∫ x, (z - x)⁻¹ ∂(rvachevMeasure F) =
      (∑ k ∈ Finset.range N, upMoment F k / z ^ (k + 1)) +
        (z ^ N)⁻¹ * ∫ x, x ^ N / (z - x) ∂(rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  have hzne : z ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hz
    linarith
  have hintpow : ∀ k : ℕ, Integrable
      (fun x : ℝ => x ^ k / z ^ (k + 1)) (rvachevMeasure F) := by
    intro k
    have h := (integrable_pow_rvachevMeasure F hF k).const_mul
      ((z ^ (k + 1))⁻¹)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [division_def, mul_comm]
  have hintrem : Integrable
      (fun x : ℝ => x ^ N / (z ^ N * (z - x))) (rvachevMeasure F) := by
    have h := (integrable_pow_div_sub_rvachevMeasure F hF hz N).const_mul
      ((z ^ N)⁻¹)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [division_def, division_def, mul_inv]
    ring
  calc ∫ x, (z - x)⁻¹ ∂(rvachevMeasure F)
      = ∫ x, ((∑ k ∈ Finset.range N, x ^ k / z ^ (k + 1)) +
          x ^ N / (z ^ N * (z - x))) ∂(rvachevMeasure F) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
        have hzx : z - x ≠ 0 := by
          have hxabs : |x| < 1 := abs_lt.mpr ⟨hx.1, hx.2⟩
          intro h0
          have : z = x := by linarith [sub_eq_zero.mp h0]
          rw [this] at hz
          linarith
        exact inv_sub_eq_sum_range_add N hzne hzx
    _ = (∑ k ∈ Finset.range N,
          ∫ x, x ^ k / z ^ (k + 1) ∂(rvachevMeasure F)) +
        ∫ x, x ^ N / (z ^ N * (z - x)) ∂(rvachevMeasure F) := by
        rw [integral_add (integrable_finsetSum _ fun k _ => hintpow k)
          hintrem, integral_finsetSum _ fun k _ => hintpow k]
    _ = (∑ k ∈ Finset.range N, upMoment F k / z ^ (k + 1)) +
        (z ^ N)⁻¹ * ∫ x, x ^ N / (z - x) ∂(rvachevMeasure F) := by
        congr 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          have hfun : (fun x : ℝ => x ^ k / z ^ (k + 1)) =
              fun x : ℝ => (z ^ (k + 1))⁻¹ * x ^ k := by
            funext x
            rw [division_def, mul_comm]
          rw [hfun, MeasureTheory.integral_const_mul, upMoment,
            division_def, mul_comm]
        · have hfun : (fun x : ℝ => x ^ N / (z ^ N * (z - x))) =
              fun x : ℝ => (z ^ N)⁻¹ * (x ^ N / (z - x)) := by
            funext x
            rw [division_def, division_def, mul_inv]
            ring
          rw [hfun, MeasureTheory.integral_const_mul]

/-- **The geometric tail bound**: the Laurent remainder decays like
`(|z|-1)⁻¹·|z|^{-N}`. -/
theorem abs_integral_inv_sub_sub_sum_le (F : BoundedFabius)
    (hF : IsFabius F) {z : ℝ} (hz : 1 < |z|) (N : ℕ) :
    |(∫ x, (z - x)⁻¹ ∂(rvachevMeasure F)) -
        ∑ k ∈ Finset.range N, upMoment F k / z ^ (k + 1)| ≤
      (|z| - 1)⁻¹ / |z| ^ N := by
  haveI := rvachevMeasure_isProbability F hF
  have hrem : (∫ x, (z - x)⁻¹ ∂(rvachevMeasure F)) -
      ∑ k ∈ Finset.range N, upMoment F k / z ^ (k + 1) =
      (z ^ N)⁻¹ * ∫ x, x ^ N / (z - x) ∂(rvachevMeasure F) := by
    rw [integral_inv_sub_eq_sum_upMoment_add F hF hz N]
    ring
  rw [hrem, abs_mul, abs_inv, abs_pow]
  have hbound : |∫ x, x ^ N / (z - x) ∂(rvachevMeasure F)| ≤
      (|z| - 1)⁻¹ := by
    have h := norm_integral_le_of_norm_le_const
      (μ := rvachevMeasure F)
      (f := fun x : ℝ => x ^ N / (z - x)) (C := (|z| - 1)⁻¹) ?_
    · rw [Real.norm_eq_abs] at h
      simpa using h
    · filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
      have hxabs : |x| ≤ 1 := le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩)
      have hle : |z| - 1 ≤ |z - x| := by
        have h := abs_sub_abs_le_abs_sub z x
        linarith
      have hpow : |x ^ N| ≤ 1 := by
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg x) hxabs
      rw [Real.norm_eq_abs, abs_div, inv_eq_one_div]
      exact div_le_div₀ (by norm_num) hpow (by linarith) hle
  calc (|z| ^ N)⁻¹ * |∫ x, x ^ N / (z - x) ∂(rvachevMeasure F)|
      ≤ (|z| ^ N)⁻¹ * (|z| - 1)⁻¹ := by
        refine mul_le_mul_of_nonneg_left hbound ?_
        positivity
    _ = (|z| - 1)⁻¹ / |z| ^ N := by
        rw [division_def]
        ring

/-- Moments of the up-measure are bounded by one. -/
theorem abs_upMoment_le_one (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) : |upMoment F k| ≤ 1 := by
  haveI := rvachevMeasure_isProbability F hF
  have h := norm_integral_le_of_norm_le_const
    (μ := rvachevMeasure F) (f := fun x : ℝ => x ^ k) (C := 1) ?_
  · rw [Real.norm_eq_abs] at h
    simpa [upMoment] using h
  · filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
    have hxabs : |x| ≤ 1 := le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg x) hxabs

/-- The Laurent series is summable: geometric comparison. -/
theorem summable_upMoment_laurent (F : BoundedFabius)
    (hF : IsFabius F) {z : ℝ} (hz : 1 < |z|) :
    Summable (fun k : ℕ => upMoment F k / z ^ (k + 1)) := by
  have hzpos : (0 : ℝ) < |z| := by linarith
  refine Summable.of_norm_bounded
    (g := fun k : ℕ => |z|⁻¹ ^ k * |z|⁻¹)
    ((summable_geometric_of_lt_one (by positivity)
      ((inv_lt_one₀ hzpos).mpr hz)).mul_right _) fun k => ?_
  rw [Real.norm_eq_abs, abs_div, abs_pow]
  calc |upMoment F k| / |z| ^ (k + 1) ≤ 1 / |z| ^ (k + 1) :=
        div_le_div₀ (by norm_num) (abs_upMoment_le_one F hF k)
          (by positivity) le_rfl
    _ = |z|⁻¹ ^ k * |z|⁻¹ := by
        rw [one_div, pow_succ, mul_inv, ← inv_pow]

/-- **The convergent moment/Laurent series**: for `|z| > 1`,
`∫ (z-x)⁻¹ dμ_up = ∑'_{k} m_k·z^{-(k+1)}`. -/
theorem integral_inv_sub_eq_tsum_upMoment (F : BoundedFabius)
    (hF : IsFabius F) {z : ℝ} (hz : 1 < |z|) :
    ∫ x, (z - x)⁻¹ ∂(rvachevMeasure F) =
      ∑' k : ℕ, upMoment F k / z ^ (k + 1) := by
  have hsum := summable_upMoment_laurent F hF hz
  have htend1 : Filter.Tendsto
      (fun N => ∑ k ∈ Finset.range N, upMoment F k / z ^ (k + 1))
      Filter.atTop
      (nhds (∑' k : ℕ, upMoment F k / z ^ (k + 1))) :=
    hsum.hasSum.tendsto_sum_nat
  have hg : Filter.Tendsto (fun N : ℕ => (|z| - 1)⁻¹ / |z| ^ N)
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun N : ℕ => (|z|⁻¹) ^ N)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        ((inv_lt_one₀ (by linarith)).mpr hz)
    have h1 := h0.const_mul ((|z| - 1)⁻¹)
    rw [mul_zero] at h1
    refine h1.congr fun N => ?_
    rw [inv_pow, division_def]
  have htend2 : Filter.Tendsto
      (fun N => ∑ k ∈ Finset.range N, upMoment F k / z ^ (k + 1))
      Filter.atTop
      (nhds (∫ x, (z - x)⁻¹ ∂(rvachevMeasure F))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun N => dist_nonneg) (fun N => ?_) hg
    rw [Real.dist_eq, abs_sub_comm]
    exact abs_integral_inv_sub_sub_sum_le F hF hz N
  exact tendsto_nhds_unique htend2 htend1

/-- `HasSum` form of the convergent Laurent expansion. -/
theorem hasSum_upMoment_laurent (F : BoundedFabius) (hF : IsFabius F)
    {z : ℝ} (hz : 1 < |z|) :
    HasSum (fun k : ℕ => upMoment F k / z ^ (k + 1))
      (∫ x, (z - x)⁻¹ ∂(rvachevMeasure F)) := by
  rw [integral_inv_sub_eq_tsum_upMoment F hF hz]
  exact (summable_upMoment_laurent F hF hz).hasSum

end Fabius

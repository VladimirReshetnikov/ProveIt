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
  Cauchy kernel, an algebraic identity;
* `integrable_inv_sub_rvachevMeasure` — integrability of the kernel
  off the support;
* `integral_inv_sub_eq_sum_upMoment_add` — the expansion with exact
  remainder;
* `abs_integral_inv_sub_sub_sum_le` — the geometric tail bound.
-/

set_option autoImplicit false

open MeasureTheory

namespace Fabius

/-- Finite geometric expansion of the Cauchy kernel:
`(z-x)⁻¹ = ∑_{k<N} x^k/z^{k+1} + x^N/(z^N(z-x))`. -/
theorem inv_sub_eq_sum_range_add (N : ℕ) {z x : ℝ} (hz : z ≠ 0)
    (hzx : z - x ≠ 0) :
    (z - x)⁻¹ = (∑ k ∈ Finset.range N, x ^ k / z ^ (k + 1)) +
      x ^ N / (z ^ N * (z - x)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep : x ^ N / z ^ (N + 1) +
        x ^ (N + 1) / (z ^ (N + 1) * (z - x)) =
        x ^ N / (z ^ N * (z - x)) := by
      field_simp
      ring
    rw [Finset.sum_range_succ, add_assoc, hstep]
    exact ih

/-- Almost every point of the up-measure lies in `(-1,1)`. -/
theorem ae_mem_Ioo_rvachevMeasure (F : BoundedFabius)
    (hF : IsFabius F) :
    ∀ᵐ x ∂(rvachevMeasure F), x ∈ Set.Ioo (-1 : ℝ) 1 := by
  haveI := rvachevMeasure_isProbability F hF
  have hcompl : rvachevMeasure F (Set.Ioo (-1 : ℝ) 1)ᶜ = 0 :=
    (prob_compl_eq_zero_iff measurableSet_Ioo).mpr
      (rvachevMeasure_Ioo_eq_one F hF)
  exact mem_ae_iff.mpr hcompl

/-- Off the support the Cauchy kernel is integrable: it is bounded by
`(|z|-1)⁻¹` almost everywhere. -/
theorem integrable_inv_sub_rvachevMeasure (F : BoundedFabius)
    (hF : IsFabius F) {z : ℝ} (hz : 1 < |z|) :
    Integrable (fun x => (z - x)⁻¹) (rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  refine Integrable.mono' (integrable_const ((|z| - 1)⁻¹))
    ((measurable_const.sub measurable_id).inv.aestronglyMeasurable) ?_
  filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
  have hxabs : |x| ≤ 1 := le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩)
  have hle : |z| - 1 ≤ |z - x| := by
    have h := abs_sub_abs_le_abs_sub z x
    linarith
  rw [norm_inv, Real.norm_eq_abs, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by linarith) hle

/-- The remainder kernel is likewise integrable. -/
theorem integrable_pow_div_sub_rvachevMeasure (F : BoundedFabius)
    (hF : IsFabius F) {z : ℝ} (hz : 1 < |z|) (N : ℕ) :
    Integrable (fun x => x ^ N / (z - x)) (rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  refine Integrable.mono' (integrable_const ((|z| - 1)⁻¹))
    (((measurable_id.pow_const N).div
      (measurable_const.sub measurable_id)).aestronglyMeasurable) ?_
  filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
  have hxabs : |x| ≤ 1 := le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩)
  have hle : |z| - 1 ≤ |z - x| := by
    have h := abs_sub_abs_le_abs_sub z x
    linarith
  have hpow : |x ^ N| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) hxabs
  rw [Real.norm_eq_abs, abs_div, inv_eq_one_div]
  exact div_le_div₀ (by norm_num) hpow (by linarith) hle

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

end Fabius

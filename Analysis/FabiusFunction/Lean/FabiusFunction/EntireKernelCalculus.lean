import FabiusFunction.StieltjesMomentLaurent

/-!
# The entire-kernel calculus of the up-measure

The transform layer's entire-kernel principle: an absolutely
summable power series integrates term by term against the up-measure,

`∫ (∑ aₙ·xⁿ) dμ_up = ∑ aₙ·mₙ`,

because the support lies in `(-1,1)` — the coefficients alone
dominate.  Any entire kernel dominated on the support (exponentials,
resolvents, trigonometric kernels) turns into an exact moment series
through this single statement; the moments are the Hankel data, so
the entire-kernel calculus, the orthogonal-polynomial layer, and the
Laurent expansion all speak the same numbers.
-/

set_option autoImplicit false

open MeasureTheory

namespace Fabius

/-- **The entire-kernel calculus**: absolutely summable power series
integrate term by term against the up-measure. -/
theorem integral_tsum_eq_tsum_upMoment (F : BoundedFabius)
    (hF : IsFabius F) {a : ℕ → ℝ} (ha : Summable fun n => |a n|) :
    ∫ x, (∑' n : ℕ, a n * x ^ n) ∂(rvachevMeasure F) =
      ∑' n : ℕ, a n * upMoment F n := by
  haveI := rvachevMeasure_isProbability F hF
  have hint : ∀ n : ℕ, Integrable (fun x : ℝ => a n * x ^ n)
      (rvachevMeasure F) :=
    fun n => (integrable_pow_rvachevMeasure F hF n).const_mul _
  have hnorm : ∀ n : ℕ,
      ∫ x, ‖a n * x ^ n‖ ∂(rvachevMeasure F) ≤ |a n| := by
    intro n
    have hle : ∀ᵐ x ∂(rvachevMeasure F), ‖a n * x ^ n‖ ≤ |a n| := by
      filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
      have hxabs : |x| ≤ 1 := le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩)
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      calc |a n| * |x| ^ n ≤ |a n| * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact pow_le_one₀ (abs_nonneg x) hxabs
        _ = |a n| := mul_one _
    calc ∫ x, ‖a n * x ^ n‖ ∂(rvachevMeasure F)
        ≤ ∫ _, |a n| ∂(rvachevMeasure F) :=
          integral_mono_ae (hint n).norm (integrable_const _) hle
      _ = |a n| := by simp
  have hsum : Summable fun n : ℕ =>
      ∫ x, ‖a n * x ^ n‖ ∂(rvachevMeasure F) :=
    Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => hnorm n) ha
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm hint
    hsum]
  refine tsum_congr fun n => ?_
  rw [MeasureTheory.integral_const_mul]
  rfl

/-- **The moment-generating series**: the exponential kernel is
entire, so the moment generating function of the up-measure is its
exact moment series, `mgf(t) = ∑ tⁿ/n!·mₙ`, for every real `t`. -/
theorem mgf_id_rvachevMeasure_eq_tsum (F : BoundedFabius)
    (hF : IsFabius F) (t : ℝ) :
    ProbabilityTheory.mgf id (rvachevMeasure F) t =
      ∑' n : ℕ, t ^ n / n.factorial * upMoment F n := by
  have hsum : Summable fun n : ℕ => |t ^ n / n.factorial| := by
    refine (Real.summable_pow_div_factorial |t|).congr fun n => ?_
    rw [abs_div, abs_pow, Nat.abs_cast]
  have hpt : ∀ x : ℝ, Real.exp (t * x) =
      ∑' n : ℕ, t ^ n / n.factorial * x ^ n := by
    intro x
    have h1 : Real.exp (t * x) = NormedSpace.exp (t * x) :=
      congrFun Real.exp_eq_exp_ℝ (t * x)
    have h2 : NormedSpace.exp (t * x) =
        ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • (t * x) ^ n :=
      congrFun NormedSpace.exp_eq_tsum (t * x)
    rw [h1, h2]
    refine tsum_congr fun n => ?_
    rw [smul_eq_mul, mul_pow]
    ring
  calc ProbabilityTheory.mgf id (rvachevMeasure F) t
      = ∫ x, Real.exp (t * x) ∂(rvachevMeasure F) := by
        simp only [ProbabilityTheory.mgf, id_eq]
    _ = ∫ x, (∑' n : ℕ, t ^ n / n.factorial * x ^ n)
          ∂(rvachevMeasure F) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hpt x)
    _ = ∑' n : ℕ, t ^ n / n.factorial * upMoment F n :=
        integral_tsum_eq_tsum_upMoment F hF hsum

end Fabius

import FabiusFunction.StieltjesHerglotz
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Poisson-kernel groundwork for the Stieltjes inversion

`Fabius.im_rvachevCauchyTransform_eq` displays the imaginary part
of the Cauchy transform of the up-measure as minus a Poisson
integral,

`Im R(x + iε) = -∫ ε/((x-t)² + ε²) dμ_up(t)`.

Stieltjes--Perron inversion runs on the kernel facts behind that
display.  This module supplies them.

* the kernel is strictly positive and bounded by `ε⁻¹` — sharply,
  and the constant cannot be improved, since equality holds at
  `t = x` (attainment is recorded as `poisson_kernel_self`);
* off a `δ`-neighbourhood of `x` it is bounded by `ε/δ²`;
* normalised by `π⁻¹` it is a probability density in `t`.  That
  density is exactly Mathlib's Cauchy law
  `ProbabilityTheory.cauchyPDFReal` with location `x` and scale
  `ε`, so the normalisation is *imported*, not re-proved;
* against the up-measure the far-field mass tends to `0` as
  `ε → 0⁺`.  This is the approximate-identity shape in the form
  the up-measure actually needs: `μ_up` is a probability measure,
  so the far-field integral is controlled by the pointwise bound
  alone;
* consequently `-π⁻¹·Im R(x + iε)` is the `μ_up`-average of a
  probability density and lies in `[0, (πε)⁻¹]`.

## Scope

The Stieltjes--Perron inversion theorem itself is *not* proved
here; it is `FabiusFunction.StieltjesPerron`.  Neither is the
Lebesgue-side approximate identity — the exact tail
`∫_{|t-x| ≥ δ} π⁻¹ε/((x-t)²+ε²) dt = 1 - (2/π)·arctan (δ/ε)` —
which needs the `arctan` antiderivative on `Ioi`/`Iic` rather than
the finite-measure bound used below; that is
`FabiusFunction.PoissonApproximateIdentity`, which imports this
module and proves the tail as
`Fabius.setIntegral_poisson_kernel_compl_Ioo` and the identity as
`Fabius.poisson_kernel_approximate_identity`.  What is established
*here* is the `μ_up`-side localisation.

## Main declarations

* `Fabius.poisson_kernel_pos` — positivity of the kernel.
* `Fabius.poisson_kernel_le_inv` — the sharp bound `≤ ε⁻¹`.
* `Fabius.poisson_kernel_le_of_le_abs` — the far-field bound
  `≤ ε/δ²` when `δ ≤ |x - t|`.
* `Fabius.integral_poisson_kernel_eq_one` — **the normalisation**
  `∫ π⁻¹·ε/((x-t)²+ε²) dt = 1`.
* `Fabius.integral_poisson_kernel_eq_pi` — the unnormalised form.
* `Fabius.integrable_poisson_kernel` — Lebesgue integrability.
* `Fabius.setIntegral_poisson_far_le` — the far-field mass bound
  against the up-measure.
* `Fabius.tendsto_setIntegral_poisson_far` — **the approximate
  identity** for the up-measure.
* `Fabius.integral_poisson_kernel_rvachevMeasure_eq` — the
  Poisson integral *is* `-Im R(x + iε)`.
* `Fabius.inv_pi_mul_neg_im_rvachevCauchyTransform_mem_Icc` —
  `-π⁻¹·Im R(x + iε) ∈ [0, (πε)⁻¹]`.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Real

namespace Fabius

/-! ### Pointwise kernel bounds -/

/-- The Poisson denominator is strictly positive for `ε > 0`. -/
theorem poisson_denom_pos (x t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 < (x - t) ^ 2 + ε ^ 2 := by
  have h1 : (0 : ℝ) ≤ (x - t) ^ 2 := sq_nonneg (x - t)
  have h2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  linarith

/-- **Positivity of the Poisson kernel**: for `ε > 0` the kernel
`t ↦ ε/((x-t)² + ε²)` is strictly positive. -/
theorem poisson_kernel_pos (x t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 < ε / ((x - t) ^ 2 + ε ^ 2) :=
  div_pos hε (poisson_denom_pos x t hε)

/-- The height bound is attained at `t = x`, so the constant `ε⁻¹` of
`poisson_kernel_le_inv` cannot be improved. -/
theorem poisson_kernel_self (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ε / ((x - x) ^ 2 + ε ^ 2) = ε⁻¹ := by
  have h0 : (x - x) ^ 2 + ε ^ 2 = ε ^ 2 := by
    rw [sub_self]
    ring
  rw [h0, pow_two, ← div_div, div_self (ne_of_gt hε), one_div]

/-- **The sharp height bound**: the Poisson kernel never exceeds
`ε⁻¹`; the constant is optimal, by `poisson_kernel_self`. -/
theorem poisson_kernel_le_inv (x t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ε / ((x - t) ^ 2 + ε ^ 2) ≤ ε⁻¹ := by
  have hsq : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have hle : ε ^ 2 ≤ (x - t) ^ 2 + ε ^ 2 := by
    have h := sq_nonneg (x - t)
    linarith
  have h1 : 1 / ((x - t) ^ 2 + ε ^ 2) ≤ 1 / ε ^ 2 :=
    one_div_le_one_div_of_le hsq hle
  have h2 : ε * (1 / ((x - t) ^ 2 + ε ^ 2)) ≤ ε * (1 / ε ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt hε)
  have h3 : ε * (1 / ε ^ 2) = ε⁻¹ := by
    rw [one_div, pow_two, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hε), one_mul]
  rw [h3] at h2
  rw [div_eq_mul_one_div ε ((x - t) ^ 2 + ε ^ 2)]
  exact h2

/-- **The far-field bound**: at distance at least `δ` from `x` the
Poisson kernel is at most `ε/δ²`. -/
theorem poisson_kernel_le_of_le_abs (x t : ℝ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (h : δ ≤ |x - t|) :
    ε / ((x - t) ^ 2 + ε ^ 2) ≤ ε / δ ^ 2 := by
  have hδsq : (0 : ℝ) < δ ^ 2 := pow_pos hδ 2
  have hsq : δ ^ 2 ≤ (x - t) ^ 2 := by
    have h1 : δ ^ 2 ≤ |x - t| ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hδ) h 2
    rwa [sq_abs] at h1
  have hle : δ ^ 2 ≤ (x - t) ^ 2 + ε ^ 2 := by
    have h2 := sq_nonneg ε
    linarith
  have h1 : 1 / ((x - t) ^ 2 + ε ^ 2) ≤ 1 / δ ^ 2 :=
    one_div_le_one_div_of_le hδsq hle
  rw [div_eq_mul_one_div ε ((x - t) ^ 2 + ε ^ 2),
    div_eq_mul_one_div ε (δ ^ 2)]
  exact mul_le_mul_of_nonneg_left h1 (le_of_lt hε)

/-! ### The kernel as Mathlib's Cauchy density -/

/-- The normalised Poisson kernel is Mathlib's Cauchy density with
location `x` and scale `ε`.  This is the bridge that imports the
normalisation instead of re-proving it. -/
private theorem poisson_eq_cauchyPDFReal (x t : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)) =
      ProbabilityTheory.cauchyPDFReal x (Real.toNNReal ε) t := by
  have hD : (x - t) ^ 2 + ε ^ 2 = (t - x) ^ 2 + ε ^ 2 := by ring
  rw [ProbabilityTheory.cauchyPDFReal_def, hD, div_eq_mul_inv,
    ← mul_assoc]
  simp only [NNReal.coe_pow, Real.coe_toNNReal',
    max_eq_left (le_of_lt hε)]

/-- **The Poisson kernel is a probability density**: for `ε > 0`,
`∫ π⁻¹·ε/((x-t)² + ε²) dt = 1`.  Imported from Mathlib's Cauchy
distribution. -/
theorem integral_poisson_kernel_eq_one (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ t : ℝ, π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)) = 1 := by
  have hγ : Real.toNNReal ε ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hε)
  refine Eq.trans ?_
    (ProbabilityTheory.integral_cauchyPDFReal_eq_one x hγ)
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun t => ?_)
  exact poisson_eq_cauchyPDFReal x t hε

/-- The Poisson kernel is Lebesgue integrable. -/
theorem integrable_poisson_kernel (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun t : ℝ => ε / ((x - t) ^ 2 + ε ^ 2)) := by
  have hpt : ∀ t : ℝ, π * ProbabilityTheory.cauchyPDFReal x
      (Real.toNNReal ε) t = ε / ((x - t) ^ 2 + ε ^ 2) := by
    intro t
    rw [← poisson_eq_cauchyPDFReal x t hε, ← mul_assoc,
      mul_inv_cancel₀ Real.pi_ne_zero, one_mul]
  have h := (ProbabilityTheory.integrable_cauchyPDFReal x
    (γ := Real.toNNReal ε)).const_mul π
  exact h.congr (Filter.Eventually.of_forall hpt)

/-- The unnormalised Poisson kernel integrates to `π`. -/
theorem integral_poisson_kernel_eq_pi (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ t : ℝ, ε / ((x - t) ^ 2 + ε ^ 2) = π := by
  have h := integral_poisson_kernel_eq_one x hε
  rw [MeasureTheory.integral_const_mul] at h
  have h2 : π * (π⁻¹ * ∫ t : ℝ, ε / ((x - t) ^ 2 + ε ^ 2)) =
      π * 1 := congrArg (fun r : ℝ => π * r) h
  rw [← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul,
    mul_one] at h2
  exact h2

/-! ### The Poisson integral of the up-measure -/

/-- The Poisson kernel is integrable against the up-measure: it is
bounded by `ε⁻¹` and the up-measure is finite. -/
theorem integrable_poisson_kernel_rvachevMeasure
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    Integrable (fun t : ℝ => ε / ((x - t) ^ 2 + ε ^ 2))
      (rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  have hmeas : Measurable
      fun t : ℝ => ε / ((x - t) ^ 2 + ε ^ 2) :=
    measurable_const.div
      (((measurable_const.sub measurable_id).pow_const 2).add
        measurable_const)
  have hb : ∀ t : ℝ, ‖ε / ((x - t) ^ 2 + ε ^ 2)‖ ≤ ε⁻¹ := by
    intro t
    rw [Real.norm_eq_abs, abs_of_pos (poisson_kernel_pos x t hε)]
    exact poisson_kernel_le_inv x t hε
  exact Integrable.mono' (integrable_const ε⁻¹)
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hb)

/-- **The far-field mass bound**: the up-measure Poisson mass
outside the `δ`-neighbourhood of `x` is at most `ε/δ²`. -/
theorem setIntegral_poisson_far_le (F : BoundedFabius)
    (hF : IsFabius F) (x : ℝ) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∫ t in (Set.Ioo (x - δ) (x + δ))ᶜ,
        ε / ((x - t) ^ 2 + ε ^ 2) ∂(rvachevMeasure F) ≤
      ε / δ ^ 2 := by
  haveI := rvachevMeasure_isProbability F hF
  have hmeas : MeasurableSet (Set.Ioo (x - δ) (x + δ))ᶜ :=
    measurableSet_Ioo.compl
  have hfar : ∀ t ∈ (Set.Ioo (x - δ) (x + δ))ᶜ, δ ≤ |x - t| := by
    intro t ht
    rw [Set.mem_compl_iff] at ht
    by_contra hcon
    push_neg at hcon
    rw [abs_lt] at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    exact ht (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
  have hint := integrable_poisson_kernel_rvachevMeasure F hF x hε
  have hnn : (0 : ℝ) ≤ ε / δ ^ 2 :=
    le_of_lt (div_pos hε (pow_pos hδ 2))
  have step1 : ∫ t in (Set.Ioo (x - δ) (x + δ))ᶜ,
      ε / ((x - t) ^ 2 + ε ^ 2) ∂(rvachevMeasure F) ≤
      ∫ _t in (Set.Ioo (x - δ) (x + δ))ᶜ,
        ε / δ ^ 2 ∂(rvachevMeasure F) := by
    refine setIntegral_mono_on hint.integrableOn
      (integrable_const (ε / δ ^ 2)).integrableOn hmeas ?_
    intro t ht
    exact poisson_kernel_le_of_le_abs x t hε hδ (hfar t ht)
  have step2 : ∫ _t in (Set.Ioo (x - δ) (x + δ))ᶜ,
      ε / δ ^ 2 ∂(rvachevMeasure F) =
      (rvachevMeasure F).real ((Set.Ioo (x - δ) (x + δ))ᶜ) *
        (ε / δ ^ 2) := by
    rw [setIntegral_const, smul_eq_mul]
  have step3 : (rvachevMeasure F).real
      ((Set.Ioo (x - δ) (x + δ))ᶜ) * (ε / δ ^ 2) ≤ ε / δ ^ 2 := by
    have h4 : (rvachevMeasure F).real
        ((Set.Ioo (x - δ) (x + δ))ᶜ) * (ε / δ ^ 2) ≤
        1 * (ε / δ ^ 2) :=
      mul_le_mul_of_nonneg_right measureReal_le_one hnn
    rwa [one_mul] at h4
  rw [step2] at step1
  exact le_trans step1 step3

/-- **Far-field localisation for the up-measure** (the concentration
half of an approximate identity; the Lebesgue-side half is
`Fabius.poisson_kernel_approximate_identity`, in the downstream
module `FabiusFunction.PoissonApproximateIdentity`): for a fixed
`x` and a fixed neighbourhood radius `δ > 0`, the Poisson mass the
kernel puts outside `(x-δ, x+δ)` tends to `0` as `ε → 0⁺`. -/
theorem tendsto_setIntegral_poisson_far (F : BoundedFabius)
    (hF : IsFabius F) (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ t in (Set.Ioo (x - δ) (x + δ))ᶜ,
          ε / ((x - t) ^ 2 + ε ^ 2) ∂(rvachevMeasure F))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hmeas : MeasurableSet (Set.Ioo (x - δ) (x + δ))ᶜ :=
    measurableSet_Ioo.compl
  have hcont : Continuous fun ε : ℝ => ε / δ ^ 2 :=
    continuous_id.div_const (δ ^ 2)
  have h0 : Filter.Tendsto (fun ε : ℝ => ε / δ ^ 2)
      (nhds (0 : ℝ)) (nhds ((0 : ℝ) / δ ^ 2)) := hcont.tendsto 0
  rw [zero_div] at h0
  have hg : Filter.Tendsto (fun ε : ℝ => ε / δ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    h0.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    exact setIntegral_nonneg hmeas fun t _ =>
      le_of_lt (poisson_kernel_pos x t hε')
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    exact setIntegral_poisson_far_le F hF x hε' hδ

/-! ### Consequences for the Cauchy transform -/

/-- The up-measure Poisson integral *is* `-Im R(x + iε)`: the
positive reading of `Fabius.im_rvachevCauchyTransform_eq`. -/
theorem integral_poisson_kernel_rvachevMeasure_eq
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ t : ℝ, ε / ((x - t) ^ 2 + ε ^ 2) ∂(rvachevMeasure F) =
      -(rvachevCauchyTransform F (x + ε * Complex.I)).im := by
  rw [im_rvachevCauchyTransform_eq F hF x (ne_of_gt hε), neg_neg]

/-- **Nonnegativity of the boundary profile**: `-Im R(x + iε) ≥ 0`
for `ε > 0`. -/
theorem neg_im_rvachevCauchyTransform_nonneg (F : BoundedFabius)
    (hF : IsFabius F) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ -(rvachevCauchyTransform F (x + ε * Complex.I)).im := by
  rw [← integral_poisson_kernel_rvachevMeasure_eq F hF x hε]
  exact integral_nonneg fun t =>
    le_of_lt (poisson_kernel_pos x t hε)

/-- **The height bound for the boundary profile**:
`-Im R(x + iε) ≤ ε⁻¹`, since the up-measure is a probability
measure and the kernel is bounded by `ε⁻¹`. -/
theorem neg_im_rvachevCauchyTransform_le_inv (F : BoundedFabius)
    (hF : IsFabius F) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    -(rvachevCauchyTransform F (x + ε * Complex.I)).im ≤ ε⁻¹ := by
  haveI := rvachevMeasure_isProbability F hF
  have hint := integrable_poisson_kernel_rvachevMeasure F hF x hε
  have hb : ∀ᵐ t : ℝ ∂(rvachevMeasure F),
      ε / ((x - t) ^ 2 + ε ^ 2) ≤ ε⁻¹ :=
    Filter.Eventually.of_forall fun t =>
      poisson_kernel_le_inv x t hε
  rw [← integral_poisson_kernel_rvachevMeasure_eq F hF x hε]
  calc ∫ t : ℝ, ε / ((x - t) ^ 2 + ε ^ 2) ∂(rvachevMeasure F)
      ≤ ∫ _t : ℝ, ε⁻¹ ∂(rvachevMeasure F) :=
        integral_mono_ae hint (integrable_const _) hb
    _ = ε⁻¹ := by
        rw [integral_const]
        simp

/-- **The density display**: `-π⁻¹·Im R(x + iε)` is the
`μ_up`-average of the normalised Poisson kernel. -/
theorem inv_pi_mul_neg_im_rvachevCauchyTransform_eq
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    π⁻¹ * (-(rvachevCauchyTransform F (x + ε * Complex.I)).im) =
      ∫ t : ℝ, π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2))
        ∂(rvachevMeasure F) := by
  rw [MeasureTheory.integral_const_mul,
    ← integral_poisson_kernel_rvachevMeasure_eq F hF x hε]

/-- **The boundary profile is a normalised density value**: for
`ε > 0`, `-π⁻¹·Im R(x + iε) ∈ [0, (πε)⁻¹]`. -/
theorem inv_pi_mul_neg_im_rvachevCauchyTransform_mem_Icc
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    π⁻¹ * (-(rvachevCauchyTransform F (x + ε * Complex.I)).im) ∈
      Set.Icc (0 : ℝ) (π * ε)⁻¹ := by
  have hπ : (0 : ℝ) ≤ π⁻¹ := le_of_lt (inv_pos.mpr Real.pi_pos)
  have h0 := neg_im_rvachevCauchyTransform_nonneg F hF x hε
  have h1 := neg_im_rvachevCauchyTransform_le_inv F hF x hε
  refine Set.mem_Icc.mpr ⟨mul_nonneg hπ h0, ?_⟩
  have h2 : π⁻¹ *
      (-(rvachevCauchyTransform F (x + ε * Complex.I)).im) ≤
      π⁻¹ * ε⁻¹ := mul_le_mul_of_nonneg_left h1 hπ
  have h3 : π⁻¹ * ε⁻¹ = (π * ε)⁻¹ := by rw [mul_inv]
  rw [h3] at h2
  exact h2

end Fabius

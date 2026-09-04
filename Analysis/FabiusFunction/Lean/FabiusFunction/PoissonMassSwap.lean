import FabiusFunction.StieltjesInversion
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The Poisson mass swap: normalisation in `x`

`FabiusFunction.StieltjesInversion` displays the boundary profile of
the Cauchy transform of the up-measure as a Poisson average,

`π⁻¹·(-Im R(x + iε)) = ∫ π⁻¹·ε/((x-t)² + ε²) dμ_up(t)`,

and brackets it in `[0, (πε)⁻¹]`.  Those statements are pointwise in
`x`.  This module integrates over `x`: for each fixed `ε > 0` the
Poisson extension of the up-measure to height `ε` is a probability
density in `x`.  "Probability density" here means nonnegative,
measurable, integrable, and of total integral `1`.  The first clause
is imported (`neg_im_rvachevCauchyTransform_nonneg`); the other
three are proved below.

The route is a Tonelli swap.  The integrand is nonnegative, so the
exchange can be run entirely in `ℝ≥0∞`, where no integrability side
condition is needed: `MeasureTheory.lintegral_lintegral_swap` asks
only for joint `AEMeasurable`ity of the uncurried integrand on
`volume.prod μ_up`, and that comes from joint continuity of the
kernel, `ε > 0` keeping the denominator away from `0`.  After the
swap the inner integral is the normalisation of the kernel *in `x`*.
That is the same statement as the normalisation in `t` only because
the kernel is even in `x - t`, so swapping its two arguments leaves it unchanged; the symmetry is
recorded as `poisson_kernel_symm` and used, not assumed.  The outer
integral is then the total mass of the probability measure `μ_up`.

## Scope

Only the fixed-`ε` normalisation is proved here.  Nothing in this
module lets `ε → 0⁺`.  Both of the things that need is are proved
elsewhere in the corpus: the Lebesgue-side approximate identity in
`PoissonApproximateIdentity`, and the Stieltjes--Perron inversion
itself in `StieltjesPerron`, which consumes this module's
normalisation together with that one.

## Main declarations

* `Fabius.poisson_kernel_symm` — the kernel sees only `x - t`.
* `Fabius.continuous_poisson_kernel_prod` — **joint continuity** of
  `(x, t) ↦ ε/((x-t)² + ε²)` on `ℝ × ℝ`.
* `Fabius.measurable_poisson_kernel_prod` — its joint measurability.
* `Fabius.measurable_ofReal_poisson_kernel_prod` — the `ℝ≥0∞` form,
  which is what the Tonelli swap consumes, weakened to
  `AEMeasurable`.
* `Fabius.inv_pi_mul_poisson_kernel_nonneg` — nonnegativity of the
  normalised kernel.
* `Fabius.integrable_poisson_kernel_swapped` — integrability in `x`
  for fixed `t`.
* `Fabius.integral_poisson_kernel_swapped_eq_one` — **the `x`-side
  normalisation** `∫ π⁻¹·ε/((x-t)² + ε²) dx = 1`.
* `Fabius.lintegral_ofReal_poisson_kernel_swapped` — its `ℝ≥0∞`
  form.
* `Fabius.ofReal_inv_pi_mul_neg_im_eq_lintegral` — the profile as an
  `ℝ≥0∞` Poisson integral.
* `Fabius.measurable_inv_pi_mul_neg_im_rvachevCauchyTransform` —
  measurability of the profile in `x`.
* `Fabius.lintegral_ofReal_inv_pi_mul_neg_im_eq_one` — **the swap**.
* `Fabius.integrable_inv_pi_mul_neg_im_rvachevCauchyTransform` —
  integrability of the profile in `x`.
* `Fabius.integral_inv_pi_mul_neg_im_rvachevCauchyTransform_eq_one`
  — **the normalisation** `∫ π⁻¹·(-Im R(x + iε)) dx = 1`.
* `Fabius.integral_neg_im_rvachevCauchyTransform_eq_pi` — the
  unnormalised form `∫ -Im R(x + iε) dx = π`.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Real

namespace Fabius

/-! ### The kernel as a function of two variables -/

/-- **The kernel sees only `x - t`**: exchanging the two arguments
leaves the Poisson kernel unchanged.  This is what makes the
`x`-normalisation and the `t`-normalisation the same statement. -/
theorem poisson_kernel_symm (x t ε : ℝ) :
    ε / ((x - t) ^ 2 + ε ^ 2) = ε / ((t - x) ^ 2 + ε ^ 2) := by
  have h : (x - t) ^ 2 = (t - x) ^ 2 := by ring
  rw [h]

/-- **Joint continuity of the Poisson kernel**: for `ε > 0` the map
`(x, t) ↦ ε/((x-t)² + ε²)` is continuous on `ℝ × ℝ`.  Positivity of
`ε` is exactly what keeps the denominator away from `0`. -/
theorem continuous_poisson_kernel_prod {ε : ℝ} (hε : 0 < ε) :
    Continuous fun p : ℝ × ℝ => ε / ((p.1 - p.2) ^ 2 + ε ^ 2) := by
  have hne : ∀ u : ℝ, u ^ 2 + ε ^ 2 ≠ 0 := by
    intro u
    have h1 : (0 : ℝ) ≤ u ^ 2 := sq_nonneg u
    have h2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
    exact ne_of_gt (by linarith)
  have hden : Continuous fun u : ℝ => u ^ 2 + ε ^ 2 := by fun_prop
  have hone : Continuous fun u : ℝ => ε / (u ^ 2 + ε ^ 2) :=
    continuous_const.div₀ hden hne
  have hsub : Continuous fun p : ℝ × ℝ => p.1 - p.2 := by fun_prop
  exact hone.comp' hsub

/-- **Joint measurability of the Poisson kernel** on `ℝ × ℝ`. -/
theorem measurable_poisson_kernel_prod {ε : ℝ} (hε : 0 < ε) :
    Measurable fun p : ℝ × ℝ => ε / ((p.1 - p.2) ^ 2 + ε ^ 2) :=
  (continuous_poisson_kernel_prod hε).measurable

/-- The normalised kernel, uncurried and pushed into `ℝ≥0∞`, is
measurable.  `MeasureTheory.lintegral_lintegral_swap` consumes the
`AEMeasurable` weakening of this. -/
theorem measurable_ofReal_poisson_kernel_prod {ε : ℝ} (hε : 0 < ε) :
    Measurable (Function.uncurry fun x t : ℝ =>
      ENNReal.ofReal (π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)))) := by
  have h : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (π⁻¹ * (ε / ((p.1 - p.2) ^ 2 + ε ^ 2))) :=
    ((measurable_poisson_kernel_prod hε).const_mul π⁻¹).ennreal_ofReal
  exact h

/-- The normalised Poisson kernel is nonnegative. -/
theorem inv_pi_mul_poisson_kernel_nonneg (x t : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    0 ≤ π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)) :=
  mul_nonneg (le_of_lt (inv_pos.mpr Real.pi_pos))
    (le_of_lt (poisson_kernel_pos x t hε))

/-! ### The kernel normalises in the other variable

The normalised Poisson kernel in `x` at height `ε` and centre `t` is
Mathlib's Cauchy probability density `cauchyPDFReal t ε`; its
integrability and normalisation are Mathlib's. -/

/-- **The normalised Poisson kernel is the Cauchy density** with
location `t` and scale `ε`. -/
theorem inv_pi_mul_poisson_kernel_eq_cauchyPDFReal (x t : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)) =
      ProbabilityTheory.cauchyPDFReal t ε.toNNReal x := by
  have hcoe : ((ε.toNNReal : ℝ)) = ε := Real.coe_toNNReal ε hε.le
  rw [ProbabilityTheory.cauchyPDFReal_def, hcoe]
  ring

/-- The normalised Poisson kernel in `x`, as a function, is the Cauchy
density. -/
theorem inv_pi_mul_poisson_kernel_fun_eq_cauchyPDFReal (t : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    (fun x : ℝ => π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2))) =
      ProbabilityTheory.cauchyPDFReal t ε.toNNReal :=
  funext fun x => inv_pi_mul_poisson_kernel_eq_cauchyPDFReal x t hε

/-- For a fixed `t`, the normalised kernel is Lebesgue integrable in
`x`: it is the Cauchy density. -/
theorem integrable_poisson_kernel_swapped (t : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    Integrable fun x : ℝ => π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)) := by
  rw [inv_pi_mul_poisson_kernel_fun_eq_cauchyPDFReal t hε]
  exact ProbabilityTheory.integrable_cauchyPDFReal t

/-- **The kernel normalises in `x` as well**: for a fixed `t` and
`ε > 0`, `∫ π⁻¹·ε/((x-t)² + ε²) dx = 1` — the Cauchy density has
total mass one. -/
theorem integral_poisson_kernel_swapped_eq_one (t : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ x : ℝ, π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)) = 1 := by
  rw [inv_pi_mul_poisson_kernel_fun_eq_cauchyPDFReal t hε]
  refine ProbabilityTheory.integral_cauchyPDFReal_eq_one t ?_
  rw [ne_eq, Real.toNNReal_eq_zero]
  exact not_le.mpr hε

/-- The `ℝ≥0∞` form of the `x`-side normalisation. -/
theorem lintegral_ofReal_poisson_kernel_swapped (t : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∫⁻ x : ℝ,
        ENNReal.ofReal (π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2))) = 1 := by
  have h := ofReal_integral_eq_lintegral_ofReal
    (integrable_poisson_kernel_swapped t hε)
    (Filter.Eventually.of_forall fun x =>
      inv_pi_mul_poisson_kernel_nonneg x t hε)
  rw [integral_poisson_kernel_swapped_eq_one t hε,
    ENNReal.ofReal_one] at h
  exact h.symm

/-! ### The boundary profile -/

/-- **The profile as an `ℝ≥0∞` Poisson integral**: pointwise in `x`,
`ofReal (π⁻¹·(-Im R(x + iε)))` is the up-measure integral of the
normalised kernel, computed in `ℝ≥0∞`. -/
theorem ofReal_inv_pi_mul_neg_im_eq_lintegral (F : BoundedFabius)
    (hF : IsFabius F) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (π⁻¹ *
        (-(rvachevCauchyTransform F (x + ε * Complex.I)).im)) =
      ∫⁻ t : ℝ, ENNReal.ofReal (π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)))
        ∂(rvachevMeasure F) := by
  rw [inv_pi_mul_neg_im_rvachevCauchyTransform_eq F hF x hε]
  exact ofReal_integral_eq_lintegral_ofReal
    ((integrable_poisson_kernel_rvachevMeasure F hF x hε).const_mul
      π⁻¹)
    (Filter.Eventually.of_forall fun t =>
      inv_pi_mul_poisson_kernel_nonneg x t hε)

/-- **Measurability of the boundary profile** in `x`: it is the
`toReal` of a Poisson `ℝ≥0∞` integral, and that integral is
measurable in `x` by the measurability half of Tonelli's theorem. -/
theorem measurable_inv_pi_mul_neg_im_rvachevCauchyTransform
    (F : BoundedFabius) (hF : IsFabius F) {ε : ℝ} (hε : 0 < ε) :
    Measurable fun x : ℝ =>
      π⁻¹ * (-(rvachevCauchyTransform F (x + ε * Complex.I)).im) := by
  haveI := rvachevMeasure_isProbability F hF
  have hinner : Measurable fun x : ℝ =>
      ∫⁻ t : ℝ, ENNReal.ofReal (π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)))
        ∂(rvachevMeasure F) :=
    (measurable_ofReal_poisson_kernel_prod hε).lintegral_prod_right
  have hfun : (fun x : ℝ =>
        π⁻¹ * (-(rvachevCauchyTransform F (x + ε * Complex.I)).im)) =
      fun x : ℝ => (∫⁻ t : ℝ,
        ENNReal.ofReal (π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)))
          ∂(rvachevMeasure F)).toReal := by
    funext x
    rw [← ofReal_inv_pi_mul_neg_im_eq_lintegral F hF x hε,
      ENNReal.toReal_ofReal
        (mul_nonneg (le_of_lt (inv_pos.mpr Real.pi_pos))
          (neg_im_rvachevCauchyTransform_nonneg F hF x hε))]
  rw [hfun]
  exact hinner.ennreal_toReal

/-- **The Poisson mass swap**: for `ε > 0` the boundary profile has
total `ℝ≥0∞` mass `1` in `x`.  Tonelli exchanges the `x`-integral
with the up-measure integral; the inner `x`-integral of the kernel is
`1` for every `t`, and `μ_up` is a probability measure. -/
theorem lintegral_ofReal_inv_pi_mul_neg_im_eq_one (F : BoundedFabius)
    (hF : IsFabius F) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ x : ℝ, ENNReal.ofReal (π⁻¹ *
        (-(rvachevCauchyTransform F (x + ε * Complex.I)).im)) = 1 := by
  haveI := rvachevMeasure_isProbability F hF
  calc ∫⁻ x : ℝ, ENNReal.ofReal (π⁻¹ *
          (-(rvachevCauchyTransform F (x + ε * Complex.I)).im))
      = ∫⁻ x : ℝ, (∫⁻ t : ℝ,
          ENNReal.ofReal (π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)))
            ∂(rvachevMeasure F)) :=
        lintegral_congr fun x =>
          ofReal_inv_pi_mul_neg_im_eq_lintegral F hF x hε
    _ = ∫⁻ t : ℝ, (∫⁻ x : ℝ,
          ENNReal.ofReal (π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2))))
            ∂(rvachevMeasure F) :=
        lintegral_lintegral_swap
          (measurable_ofReal_poisson_kernel_prod hε).aemeasurable
    _ = ∫⁻ _t : ℝ, 1 ∂(rvachevMeasure F) :=
        lintegral_congr fun t =>
          lintegral_ofReal_poisson_kernel_swapped t hε
    _ = 1 := by rw [lintegral_one, rvachevMeasure_univ F hF]

/-- **The profile is integrable in `x`**: for `ε > 0` the function
`x ↦ π⁻¹·(-Im R(x + iε))` is Lebesgue integrable, its total mass
being `1`. -/
theorem integrable_inv_pi_mul_neg_im_rvachevCauchyTransform
    (F : BoundedFabius) (hF : IsFabius F) {ε : ℝ} (hε : 0 < ε) :
    Integrable fun x : ℝ =>
      π⁻¹ * (-(rvachevCauchyTransform F (x + ε * Complex.I)).im) := by
  have hnn : 0 ≤ᵐ[volume] fun x : ℝ =>
      π⁻¹ * (-(rvachevCauchyTransform F (x + ε * Complex.I)).im) :=
    Filter.Eventually.of_forall fun x =>
      mul_nonneg (le_of_lt (inv_pos.mpr Real.pi_pos))
        (neg_im_rvachevCauchyTransform_nonneg F hF x hε)
  have hfin : (∫⁻ x : ℝ, ENNReal.ofReal (π⁻¹ *
      (-(rvachevCauchyTransform F (x + ε * Complex.I)).im))) < ⊤ := by
    rw [lintegral_ofReal_inv_pi_mul_neg_im_eq_one F hF hε]
    exact ENNReal.one_lt_top
  exact ⟨(measurable_inv_pi_mul_neg_im_rvachevCauchyTransform F hF
      hε).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal hnn).mpr hfin⟩

/-- **The Tonelli normalisation**: for each fixed `ε > 0` the Poisson
extension of the up-measure to height `ε` is itself a probability
density in `x`, `∫ π⁻¹·(-Im R(x + iε)) dx = 1`. -/
theorem integral_inv_pi_mul_neg_im_rvachevCauchyTransform_eq_one
    (F : BoundedFabius) (hF : IsFabius F) {ε : ℝ} (hε : 0 < ε) :
    ∫ x : ℝ, π⁻¹ *
        (-(rvachevCauchyTransform F (x + ε * Complex.I)).im) = 1 := by
  have hnn : 0 ≤ᵐ[volume] fun x : ℝ =>
      π⁻¹ * (-(rvachevCauchyTransform F (x + ε * Complex.I)).im) :=
    Filter.Eventually.of_forall fun x =>
      mul_nonneg (le_of_lt (inv_pos.mpr Real.pi_pos))
        (neg_im_rvachevCauchyTransform_nonneg F hF x hε)
  rw [integral_eq_lintegral_of_nonneg_ae hnn
      (measurable_inv_pi_mul_neg_im_rvachevCauchyTransform F hF
        hε).aestronglyMeasurable,
    lintegral_ofReal_inv_pi_mul_neg_im_eq_one F hF hε,
    ENNReal.toReal_one]

/-- **The unnormalised form**: `∫ -Im R(x + iε) dx = π` for
`ε > 0`. -/
theorem integral_neg_im_rvachevCauchyTransform_eq_pi
    (F : BoundedFabius) (hF : IsFabius F) {ε : ℝ} (hε : 0 < ε) :
    ∫ x : ℝ, -(rvachevCauchyTransform F (x + ε * Complex.I)).im =
      π := by
  have h :=
    integral_inv_pi_mul_neg_im_rvachevCauchyTransform_eq_one F hF hε
  rw [MeasureTheory.integral_const_mul] at h
  have h2 : π * (π⁻¹ *
      ∫ x : ℝ, -(rvachevCauchyTransform F (x + ε * Complex.I)).im) =
      π * 1 := congrArg (fun r : ℝ => π * r) h
  rw [← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul,
    mul_one] at h2
  exact h2

end Fabius

import FabiusFunction.NegativeLaplace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Laplace transform of the Fabius distribution function

This module supplies the exact analytic bridge between the entire generating
function used in the arithmetic theory and the one-sided Laplace transform of
the Fabius distribution function.  For `Re z > 0`, it proves

`complexGeneratingFunction F (-z) / z = ∫ t in (0, ∞), F(t) exp(-zt)`.

It also records the real-axis specialization

`generatingFunction F (-s) / s = ∫ t in (0, ∞), F(t) exp(-st)`

for `s > 0`, together with the real integrability fact needed to use that
formula without repeatedly passing through complex-valued integrals.  The
complex integrand is separately exposed as integrable for `Re z > 0`, with
the uniform transform bound `‖L(z)‖ ≤ 1 / Re z` and its real-axis corollary.

The proof first rewrites the Rvachev bump as `1 - F` on `[0, 1]`, integrates
the constant exponential explicitly, and then uses the convention `F(t) = 1`
for `t ≥ 1` to identify the remaining exponential with the tail integral.
This form is suited to Fourier inversion on a vertical line and hence to the
quantitative saddle-point framework.
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Interval

namespace Fabius

/-- On the unit interval, the Rvachev bump is the complementary Fabius CDF. -/
theorem rvachevUp_eq_one_sub_fabiusReal_of_mem_Icc
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    rvachevUp F t = 1 - fabiusReal F t := by
  rw [rvachevUp]
  split_ifs with h
  · have ht0 : t = 0 := le_antisymm h ht.1
    subst t
    norm_num
    change fabiusReal F 1 = 1 - fabiusReal F 0
    rw [hF.one_of_one_le 1 le_rfl, hF.zero_of_nonpos 0 le_rfl]
    norm_num
  · exact hF.symmetry t ht

/-- Sharp form of `rvachevUp_eq_one_sub_fabiusReal_of_mem_Icc`: on the whole
nonnegative ray, and not merely on `[0, 1]`, Rvachev's bump is the
complementary Fabius CDF.

No upper endpoint restriction is needed, because `IsFabius.symmetry_all`
already extends the reflection identity `F (1 - x) = 1 - F x` from `Icc 0 1`
to all of `ℝ` using the two constant tails.  The remaining hypothesis `0 ≤ t`
is sharp: at `t = -1/2` the left side is `fabiusReal F (1/2) = 1/2` while the
right side is `1 - fabiusReal F (-1/2) = 1`.

It is placed next to the `Icc` form rather than in `FabiusFunction.Basic`,
where the ingredients `rvachevUp_of_nonpos`, `rvachevUp_of_pos` and
`IsFabius.symmetry_all` live, so that the root of the import graph stays
untouched.  The nonnegative-ray unfolding is re-derived here because
`rvachevUp_eq_fabiusReal_one_sub` in `FabiusFunction.Monotonicity` is not in
this module's import closure. -/
theorem rvachevUp_eq_one_sub_fabiusReal_of_nonneg
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ} (ht : 0 ≤ t) :
    rvachevUp F t = 1 - fabiusReal F t := by
  have hup : rvachevUp F t = fabiusReal F (1 - t) := by
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, rvachevUp_of_nonpos F le_rfl]
      norm_num
    · exact rvachevUp_of_pos F h
  rw [hup, hF.symmetry_all t]

/-- Pointwise domination of the complex Fabius--Laplace integrand by the
real exponential determined by the real part of the parameter. -/
theorem norm_fabiusReal_mul_cexp_neg_le
    (F : BoundedFabius) (z : ℂ) (t : ℝ) :
    ‖(fabiusReal F t : ℂ) * Complex.exp (-z * t)‖ ≤
      Real.exp (-z.re * t) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fabiusReal_nonneg F t), Complex.norm_exp]
  have hre : (-z * (t : ℂ)).re = -z.re * t := by
    simp
  rw [hre]
  exact mul_le_of_le_one_left (Real.exp_nonneg _)
    (fabiusReal_le_one F t)

/-- Continuity of the complex Fabius--Laplace integrand for every complex
parameter. -/
theorem continuous_fabiusReal_mul_cexp_neg
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    Continuous (fun t : ℝ =>
      (fabiusReal F t : ℂ) * Complex.exp (-z * t)) :=
  (Complex.continuous_ofReal.comp hF.contDiff.continuous).mul (by fun_prop)

/-- The complex Fabius--Laplace integrand is integrable on the positive
half-line whenever the parameter lies in the open right half-plane. -/
theorem integrableOn_fabiusReal_mul_cexp_neg
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ =>
      (fabiusReal F t : ℂ) * Complex.exp (-z * t)) (Ioi 0) := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-z.re * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (a := -z.re) (by linarith) 0
  apply hexp.mono'
  · exact (continuous_fabiusReal_mul_cexp_neg F hF z).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t =>
      norm_fabiusReal_mul_cexp_neg_le F z t

/-- Uniform half-plane bound for the one-sided complex Laplace transform. -/
theorem norm_integral_fabiusReal_mul_cexp_neg_le
    (F : BoundedFabius) {z : ℂ} (hz : 0 < z.re) :
    ‖∫ t : ℝ in Ioi 0,
        (fabiusReal F t : ℂ) * Complex.exp (-z * t)‖ ≤
      (z.re)⁻¹ := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-z.re * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (a := -z.re) (by linarith) 0
  calc
    ‖∫ t : ℝ in Ioi 0,
        (fabiusReal F t : ℂ) * Complex.exp (-z * t)‖ ≤
        ∫ t : ℝ in Ioi 0, Real.exp (-z.re * t) := by
      apply norm_integral_le_of_norm_le hexp
      exact Filter.Eventually.of_forall fun t =>
        norm_fabiusReal_mul_cexp_neg_le F z t
    _ = (z.re)⁻¹ := by
      rw [integral_exp_mul_Ioi (a := -z.re) (by linarith) 0]
      simp [div_eq_mul_inv]

/-- Integration by parts in algebraic form: `G(-z)` is the endpoint
exponential plus `z` times the finite-interval Laplace transform of `F`. -/
theorem complexGeneratingFunction_neg_eq_exp_add_integral
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ} (hz : z ≠ 0) :
    complexGeneratingFunction F (-z) =
      Complex.exp (-z) + z * ∫ t in (0 : ℝ)..1,
        (fabiusReal F t : ℂ) * Complex.exp (-z * t) := by
  let e : ℝ → ℂ := fun t => Complex.exp (-z * t)
  let f : ℝ → ℂ := fun t => (fabiusReal F t : ℂ) * e t
  have he : Continuous e := by
    dsimp [e]
    fun_prop
  have hf : Continuous f := by
    dsimp [f]
    exact (Complex.continuous_ofReal.comp (hF.contDiff.continuous)).mul he
  have hrewrite :
      (∫ t in (0 : ℝ)..1,
        (rvachevUp F t : ℂ) * Complex.exp (-z * t)) =
      (∫ t in (0 : ℝ)..1, e t - f t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
    rw [rvachevUp_eq_one_sub_fabiusReal_of_mem_Icc F hF ht']
    simp only [e, f]
    push_cast
    ring
  have hsplit : (∫ t in (0 : ℝ)..1, e t - f t) =
      (∫ t in (0 : ℝ)..1, e t) - ∫ t in (0 : ℝ)..1, f t := by
    exact intervalIntegral.integral_sub (he.intervalIntegrable 0 1)
      (hf.intervalIntegrable 0 1)
  have hexp : (∫ t in (0 : ℝ)..1, e t) =
      (1 - Complex.exp (-z)) / z := by
    rw [show (∫ t in (0 : ℝ)..1, e t) =
        (Complex.exp ((-z) * 1) - Complex.exp ((-z) * 0)) / (-z) by
      exact integral_exp_mul_complex (neg_ne_zero.mpr hz)]
    simp
    ring
  rw [complexGeneratingFunction, neg_mul, hrewrite, hsplit, hexp]
  dsimp [f, e]
  field_simp
  ring

/-- Finite-interval form of the one-sided Laplace-transform identity. -/
theorem complexGeneratingFunction_neg_div_eq_interval_add_tail
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ} (hz : z ≠ 0) :
    complexGeneratingFunction F (-z) / z =
      (∫ t in (0 : ℝ)..1,
        (fabiusReal F t : ℂ) * Complex.exp (-z * t)) +
        Complex.exp (-z) / z := by
  rw [complexGeneratingFunction_neg_eq_exp_add_integral F hF hz]
  field_simp
  ring

/-- Exact one-sided Laplace transform of the Fabius distribution function.

The half-plane assumption guarantees convergence of the exponential tail. -/
theorem complexGeneratingFunction_neg_div_eq_laplace
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ}
    (hz : 0 < z.re) :
    complexGeneratingFunction F (-z) / z =
      ∫ t : ℝ in Ioi 0,
        (fabiusReal F t : ℂ) * Complex.exp (-z * t) := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  let f : ℝ → ℂ := fun t =>
    (fabiusReal F t : ℂ) * Complex.exp (-z * t)
  have hf : Continuous f := by
    dsimp [f]
    exact continuous_fabiusReal_mul_cexp_neg F hF z
  have htail_eq : Set.EqOn f (fun t : ℝ => Complex.exp ((-z) * t)) (Ioi 1) := by
    intro t ht
    dsimp [f]
    have hFt : fabiusReal F t = 1 := by
      exact hF.one_of_one_le t ht.le
    change (fabiusReal F t : ℂ) * Complex.exp (-z * t) = Complex.exp (-z * t)
    rw [hFt]
    norm_num
  have htail_exp : IntegrableOn (fun t : ℝ => Complex.exp ((-z) * t)) (Ioi 1) :=
    integrableOn_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 1
  have htail : IntegrableOn f (Ioi 1) :=
    htail_exp.congr_fun htail_eq.symm measurableSet_Ioi
  have htail_integral : (∫ t : ℝ in Ioi 1, f t) = Complex.exp (-z) / z := by
    rw [setIntegral_congr_fun measurableSet_Ioi htail_eq,
      integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 1]
    norm_num
  calc
    complexGeneratingFunction F (-z) / z =
        (∫ t in (0 : ℝ)..1, f t) + Complex.exp (-z) / z := by
      simpa [f] using complexGeneratingFunction_neg_div_eq_interval_add_tail F hF hz0
    _ = (∫ t in (0 : ℝ)..1, f t) + ∫ t : ℝ in Ioi 1, f t := by
      rw [htail_integral]
    _ = ∫ t : ℝ in Ioi 0, f t :=
      intervalIntegral.integral_interval_add_Ioi' (hf.intervalIntegrable 0 1) htail
    _ = ∫ t : ℝ in Ioi 0,
        (fabiusReal F t : ℂ) * Complex.exp (-z * t) := by rfl

/-- The quotient form of the negative generating function inherits the
sharp elementary half-plane bound from its Laplace representation. -/
theorem norm_complexGeneratingFunction_neg_div_le_inv_re
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ} (hz : 0 < z.re) :
    ‖complexGeneratingFunction F (-z) / z‖ ≤ (z.re)⁻¹ := by
  rw [complexGeneratingFunction_neg_div_eq_laplace F hF hz]
  exact norm_integral_fabiusReal_mul_cexp_neg_le F hz

/-- The real Laplace integrand is integrable on the positive half-line.

This reusable real-valued form avoids reconstructing measurability and
domination by the decaying exponential in applications of the Laplace
identity. -/
theorem integrableOn_fabiusReal_mul_exp_neg
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ =>
      fabiusReal F t * Real.exp (-s * t)) (Ioi 0) := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-s * t)) (Ioi 0) := by
    convert integrableOn_exp_mul_Ioi (a := -s) (by linarith) 0 using 1
  apply hexp.mono'
  · exact (hF.contDiff.continuous.mul
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (fabiusReal_nonneg F t) (Real.exp_nonneg _))]
    exact mul_le_of_le_one_left (Real.exp_nonneg _)
      (fabiusReal_le_one F t)

/-- Real-axis form of the one-sided Laplace-transform identity.

Although this follows from the complex identity by restricting to positive
real parameters, keeping the real statement in the public API eliminates
coercion bookkeeping in positivity and comparison arguments. -/
theorem generatingFunction_neg_div_eq_laplace
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    generatingFunction F (-s) / s =
      ∫ t : ℝ in Ioi 0,
        fabiusReal F t * Real.exp (-s * t) := by
  have h := complexGeneratingFunction_neg_div_eq_laplace F hF
    (z := (s : ℂ)) (by simpa using hs)
  let g : ℝ → ℝ := fun t =>
    fabiusReal F t * Real.exp (-s * t)
  have hintegrand :
      (fun t : ℝ =>
        (fabiusReal F t : ℂ) * Complex.exp (-(s : ℂ) * t)) =
        fun t : ℝ => (g t : ℂ) := by
    funext t
    dsimp [g]
    push_cast
    rfl
  have hgcast :
      (∫ t : ℝ in Ioi 0, (g t : ℂ)) =
        Complex.ofReal (∫ t : ℝ in Ioi 0, g t) := by
    exact integral_ofReal (𝕜 := ℂ)
  rw [hintegrand, hgcast] at h
  have hneg : -(s : ℂ) = ((-s : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hneg, complexGeneratingFunction_ofReal] at h
  have hcast :
      Complex.ofReal (generatingFunction F (-s) / s) =
        Complex.ofReal (∫ t : ℝ in Ioi 0, g t) := by
    simpa using h
  exact Complex.ofReal_injective hcast

/-- Real-axis specialization of the half-plane quotient bound. -/
theorem abs_generatingFunction_neg_div_le_inv
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    |generatingFunction F (-s) / s| ≤ s⁻¹ := by
  have h := norm_complexGeneratingFunction_neg_div_le_inv_re F hF
    (z := (s : ℂ)) (by simpa using hs)
  rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by simp,
    complexGeneratingFunction_ofReal] at h
  simpa [abs_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using h

end Fabius

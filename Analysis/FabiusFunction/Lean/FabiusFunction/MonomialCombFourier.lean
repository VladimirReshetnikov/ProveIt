import FabiusFunction.PoissonSummation
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Monomial Rvachev Schwartz functions and their Fourier transforms

Stage one of the shifted dyadic exactness theorem of the comb volume
(`h∑_k P(h(k+θ))·up(h(k+θ)) = ∫ P·up` for `deg P ≤ m`, `h = 2^{-m}`):
the weighted samples come from the functions `x ↦ x^p·up(u·x)`, which
this module packages as Schwartz maps and whose Fourier transforms it
expresses through derivatives of the scaled transform:

* `monomialRvachevSchwartz F hF p u hu` — `x^p·up(u·x)` as a complex
  Schwartz map (smooth with compact support);
* `fourier_monomialRvachevSchwartz` —
  `(-2πi)^p • 𝓕(x^p·up(u·x))(w) = (𝓕(up(u·)))⁽ᵖ⁾(w)`, by Mathlib's
  `Real.iteratedDeriv_fourier`.

The later stages evaluate the right side through the analytic
transform `rvachevFourier` and its integer-zero orders, and assemble
Poisson summation into the exactness statement.
-/

set_option autoImplicit false

open MeasureTheory Real Complex
open scoped ContDiff FourierTransform SchwartzMap

namespace Fabius

/-- `x^p·up(u·x)` as a complex Schwartz map. -/
noncomputable def monomialRvachevSchwartz (F : BoundedFabius)
    (hF : IsFabius F) (p : ℕ) (u : ℝ) (hu : u ≠ 0) : SchwartzMap ℝ ℂ := by
  let f : ℝ → ℝ := fun x => x ^ p * rvachevUp F (u * x)
  have hf_compact : HasCompactSupport f := by
    have hbase : HasCompactSupport (fun x : ℝ => rvachevUp F (u * x)) := by
      simpa only [smul_eq_mul] using
        (rvachevUp_hasCompactSupport F hF).comp_smul hu
    exact hbase.mul_left
  have hf_smooth : ContDiff ℝ ∞ f :=
    (contDiff_id.pow p).mul ((rvachev_contDiff F hF).comp (by fun_prop))
  exact (hf_compact.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hf_smooth)

@[simp] theorem monomialRvachevSchwartz_apply (F : BoundedFabius)
    (hF : IsFabius F) (p : ℕ) (u : ℝ) (hu : u ≠ 0) (x : ℝ) :
    monomialRvachevSchwartz F hF p u hu x =
      ((x ^ p * rvachevUp F (u * x) : ℝ) : ℂ) :=
  rfl

/-- The scaled Schwartz map's monomial weights are integrable. -/
theorem integrable_pow_smul_scaledRvachevSchwartz (F : BoundedFabius)
    (hF : IsFabius F) {u : ℝ} (hu : u ≠ 0) (k : ℕ) :
    Integrable
      (fun x : ℝ => x ^ k • scaledRvachevSchwartz F hF u hu x) := by
  refine ((monomialRvachevSchwartz F hF k u hu).integrable
    (μ := volume)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [monomialRvachevSchwartz_apply, scaledRvachevSchwartz_apply,
    Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow]

/-- **The Fourier transform of the monomial sample function** is a
derivative of the scaled transform:
`(-2πi)^p • 𝓕(x^p·up(u·x))(w) = (𝓕(up(u·)))⁽ᵖ⁾(w)`. -/
theorem fourier_monomialRvachevSchwartz (F : BoundedFabius)
    (hF : IsFabius F) (p : ℕ) {u : ℝ} (hu : u ≠ 0) (w : ℝ) :
    (-(2 * (Real.pi : ℂ) * Complex.I)) ^ p •
        𝓕 (⇑(monomialRvachevSchwartz F hF p u hu)) w =
      iteratedDeriv p (𝓕 (⇑(scaledRvachevSchwartz F hF u hu))) w := by
  have hint : ∀ (k : ℕ), (k : ℕ∞) ≤ (p : ℕ∞) →
      Integrable
        (fun x : ℝ => x ^ k • scaledRvachevSchwartz F hF u hu x) :=
    fun k _ => integrable_pow_smul_scaledRvachevSchwartz F hF hu k
  rw [Real.iteratedDeriv_fourier hint le_rfl]
  have hfun : (fun x : ℝ =>
      (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ p •
        scaledRvachevSchwartz F hF u hu x) =
      fun x : ℝ => (-(2 * (Real.pi : ℂ) * Complex.I)) ^ p •
        monomialRvachevSchwartz F hF p u hu x := by
    funext x
    simp only [monomialRvachevSchwartz_apply, scaledRvachevSchwartz_apply,
      smul_eq_mul, mul_pow, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  rw [hfun]
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  rw [smul_comm]

end Fabius

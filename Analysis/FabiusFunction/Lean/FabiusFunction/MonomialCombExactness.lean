import FabiusFunction.MonomialCombAlias

/-!
# Shifted dyadic exactness of the monomial Rvachev combs

The finale of the arc: Poisson summation for the monomial sample
function, with every nonzero alias killed by
`fourier_monomialRvachevSchwartz_int_eq_zero`, collapses the shifted
comb sum to the zero-frequency term — the integral.

* `tsum_shifted_monomial_eq_integral` — the complex-valued form:
  `∑_{k∈ℤ} (θ+k)^p·up(2^{-m}(θ+k)) = ∫ x^p·up(2^{-m}x) dx` for every
  shift `θ` and every `p ≤ m`.
* `tsum_shifted_monomial_eq_integral_real` — the real-valued form.

This is the comb volume's *shifted dyadic exactness* theorem for
monomials (linearity in `P` gives the polynomial statement): the
level-`m` dyadic comb integrates every polynomial of degree at most
`m` against `up` exactly, uniformly in the real shift.
-/

set_option autoImplicit false

open MeasureTheory Real Complex
open scoped ContDiff FourierTransform SchwartzMap

namespace Fabius

/-- **Shifted dyadic exactness, complex form**: for `p ≤ m` and every
real shift `θ`, the shifted comb sum of `x^p·up(2^{-m}x)` equals its
integral. -/
theorem tsum_shifted_monomial_eq_integral (F : BoundedFabius)
    (hF : IsFabius F) (m : ℕ) {p : ℕ} (hp : p ≤ m) (θ : ℝ) :
    ∑' k : ℤ, monomialRvachevSchwartz F hF p ((2 : ℝ) ^ m)⁻¹
        (by positivity) (θ + k) =
      ∫ x : ℝ, ((x ^ p * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x) : ℝ) : ℂ) := by
  set f := monomialRvachevSchwartz F hF p ((2 : ℝ) ^ m)⁻¹
    (by positivity) with hfdef
  have hpois := f.tsum_eq_tsum_fourier θ
  have hvanish : ∀ ℓ : ℤ, ℓ ≠ 0 →
      𝓕 f ℓ * fourier ℓ (θ : UnitAddCircle) = 0 := by
    intro ℓ hℓ
    have h0 : (𝓕 f) ((ℓ : ℤ) : ℝ) = 0 :=
      fourier_monomialRvachevSchwartz_int_eq_zero F hF m hp hℓ
    rw [h0, zero_mul]
  rw [hpois, tsum_eq_single (0 : ℤ) hvanish, fourier_zero, mul_one]
  have h00 : (((0 : ℤ) : ℝ)) = (0 : ℝ) := by norm_num
  show 𝓕 (⇑f) (((0 : ℤ) : ℝ)) = _
  rw [h00, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  simp [hfdef, monomialRvachevSchwartz_apply]

/-- **Shifted dyadic exactness, real form**: for `p ≤ m` and every
real shift `θ`,
`∑_{k∈ℤ} (θ+k)^p·up(2^{-m}(θ+k)) = ∫ x^p·up(2^{-m}x) dx`. -/
theorem tsum_shifted_monomial_eq_integral_real (F : BoundedFabius)
    (hF : IsFabius F) (m : ℕ) {p : ℕ} (hp : p ≤ m) (θ : ℝ) :
    ∑' k : ℤ, (θ + k) ^ p * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * (θ + k)) =
      ∫ x : ℝ, x ^ p * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  calc ∑' k : ℤ, (((θ + k) ^ p *
        rvachevUp F (((2 : ℝ) ^ m)⁻¹ * (θ + k)) : ℝ) : ℂ)
      = ∑' k : ℤ, monomialRvachevSchwartz F hF p ((2 : ℝ) ^ m)⁻¹
          (by positivity) (θ + k) := rfl
    _ = ∫ x : ℝ,
          ((x ^ p * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x) : ℝ) : ℂ) :=
        tsum_shifted_monomial_eq_integral F hF m hp θ
    _ = ((∫ x : ℝ, x ^ p * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x) : ℝ) : ℂ) :=
        integral_ofReal

end Fabius

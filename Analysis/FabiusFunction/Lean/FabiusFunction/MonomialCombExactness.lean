import FabiusFunction.MonomialCombAlias

/-!
# Shifted exactness of the monomial Rvachev combs

The finale of the arc: Poisson summation for the monomial sample
function, with every nonzero alias killed by
`fourier_monomialRvachevSchwartz_nat_int_eq_zero`, collapses the
shifted comb sum to the zero-frequency term — the integral.  The
statement holds on every integer mesh `M ≥ 1` up to degree `v₂(M)`;
the dyadic mesh `M = 2^m` is the instance with `v₂(M) = m`.

* `tsum_shifted_monomial_eq_integral_nat` — the complex-valued form:
  `∑_{k∈ℤ} (θ+k)^p·up((θ+k)/M) = ∫ x^p·up(x/M) dx` for every shift
  `θ` and every `p ≤ v₂(M)`.
* `tsum_shifted_monomial_eq_integral_nat_real` — the real-valued form.
* `tsum_shifted_monomial_eq_integral`,
  `tsum_shifted_monomial_eq_integral_real` — the dyadic instances.

This is the comb volume's *shifted dyadic exactness* theorem for
monomials (linearity in `P` gives the polynomial statement): the
level-`m` dyadic comb integrates every polynomial of degree at most
`m` against `up` exactly, uniformly in the real shift.
-/

set_option autoImplicit false

open MeasureTheory Real Complex
open scoped ContDiff FourierTransform SchwartzMap

namespace Fabius

/-- **Shifted exactness on integer meshes, complex form**: for
`p ≤ v₂(M)` and every real shift `θ`, the shifted comb sum of
`x^p·up(x/M)` equals its integral. -/
theorem tsum_shifted_monomial_eq_integral_nat (F : BoundedFabius)
    (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) {p : ℕ}
    (hp : p ≤ padicValNat 2 M) (θ : ℝ) :
    ∑' k : ℤ, monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
        (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) (θ + k) =
      ∫ x : ℝ, ((x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) := by
  set f := monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
    (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) with hfdef
  have hpois := f.tsum_eq_tsum_fourier θ
  have hvanish : ∀ ℓ : ℤ, ℓ ≠ 0 →
      𝓕 f ℓ * fourier ℓ (θ : UnitAddCircle) = 0 := by
    intro ℓ hℓ
    have h0 : (𝓕 f) ((ℓ : ℤ) : ℝ) = 0 :=
      fourier_monomialRvachevSchwartz_nat_int_eq_zero F hF hM hp hℓ
    rw [h0, zero_mul]
  rw [hpois, tsum_eq_single (0 : ℤ) hvanish, fourier_zero, mul_one]
  have h00 : (((0 : ℤ) : ℝ)) = (0 : ℝ) := by norm_num
  show 𝓕 (⇑f) (((0 : ℤ) : ℝ)) = _
  rw [h00, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  simp [hfdef, monomialRvachevSchwartz_apply]

/-- **Shifted exactness on integer meshes, real form**: for
`p ≤ v₂(M)` and every real shift `θ`,
`∑_{k∈ℤ} (θ+k)^p·up((θ+k)/M) = ∫ x^p·up(x/M) dx`. -/
theorem tsum_shifted_monomial_eq_integral_nat_real (F : BoundedFabius)
    (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) {p : ℕ}
    (hp : p ≤ padicValNat 2 M) (θ : ℝ) :
    ∑' k : ℤ, (θ + k) ^ p * rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) =
      ∫ x : ℝ, x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  calc ∑' k : ℤ, (((θ + k) ^ p *
        rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) : ℝ) : ℂ)
      = ∑' k : ℤ, monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
          (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) (θ + k) := rfl
    _ = ∫ x : ℝ,
          ((x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) :=
        tsum_shifted_monomial_eq_integral_nat F hF hM hp θ
    _ = ((∫ x : ℝ, x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) :=
        integral_ofReal

/-- **Shifted dyadic exactness, complex form**: for `p ≤ m` and every
real shift `θ`, the shifted comb sum of `x^p·up(2^{-m}x)` equals its
integral — the instance `M = 2^m` of the integer-mesh theorem. -/
theorem tsum_shifted_monomial_eq_integral (F : BoundedFabius)
    (hF : IsFabius F) (m : ℕ) {p : ℕ} (hp : p ≤ m) (θ : ℝ) :
    ∑' k : ℤ, monomialRvachevSchwartz F hF p ((2 : ℝ) ^ m)⁻¹
        (by positivity) (θ + k) =
      ∫ x : ℝ, ((x ^ p * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x) : ℝ) : ℂ) := by
  have h := tsum_shifted_monomial_eq_integral_nat F hF (M := 2 ^ m)
    (pow_ne_zero m two_ne_zero) (p := p)
    (by rw [padicValNat.prime_pow]; exact hp) θ
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- **Shifted dyadic exactness, real form**: for `p ≤ m` and every
real shift `θ`,
`∑_{k∈ℤ} (θ+k)^p·up(2^{-m}(θ+k)) = ∫ x^p·up(2^{-m}x) dx`. -/
theorem tsum_shifted_monomial_eq_integral_real (F : BoundedFabius)
    (hF : IsFabius F) (m : ℕ) {p : ℕ} (hp : p ≤ m) (θ : ℝ) :
    ∑' k : ℤ, (θ + k) ^ p * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * (θ + k)) =
      ∫ x : ℝ, x ^ p * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x) := by
  have h := tsum_shifted_monomial_eq_integral_nat_real F hF (M := 2 ^ m)
    (pow_ne_zero m two_ne_zero) (p := p)
    (by rw [padicValNat.prime_pow]; exact hp) θ
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

end Fabius

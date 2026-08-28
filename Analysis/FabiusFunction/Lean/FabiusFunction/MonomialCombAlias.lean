import FabiusFunction.MonomialCombDerivatives
import FabiusFunction.IntegerZeroAnalyticOrder

/-!
# Alias vanishing for the dyadic monomial combs

Stage three (first half) of the shifted dyadic exactness theorem: at
the dyadic scale `u = 2^{-m}`, every nonzero-frequency alias of the
monomial sample function vanishes for `p ≤ m`.

* `iteratedDeriv_rvachevFourier_two_pow_int_eq_zero` — the complex
  derivatives of the transform of order `p ≤ m` vanish at `2^m·ℓ`
  (`ℓ ≠ 0`): the integer-zero order there is `v₂(2^m ℓ)+1 ≥ m+1`.
* `fourier_monomialRvachevSchwartz_int_eq_zero` — hence the Fourier
  transform of `x^p·up(2^{-m}x)` vanishes at every nonzero integer
  frequency: through the identities of stages one and two, that
  transform is a nonzero multiple of the vanishing derivative.

The second half assembles Poisson summation: with all nonzero
aliases gone, the shifted comb sum equals the zero-frequency term,
the integral.
-/

set_option autoImplicit false

open MeasureTheory Real Complex
open scoped ContDiff FourierTransform SchwartzMap

namespace Fabius

/-- Derivatives of order `p ≤ m` of the analytic transform vanish at
the nonzero multiples of `2^m`. -/
theorem iteratedDeriv_rvachevFourier_two_pow_int_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) {ℓ : ℤ}
    (hℓ : ℓ ≠ 0) {p : ℕ} (hp : p ≤ m) :
    iteratedDeriv p (rvachevFourier F) ((2 : ℂ) ^ m * (ℓ : ℂ)) = 0 := by
  have hfun : rvachevFourier F = rvachevFourierProduct :=
    funext (rvachevFourier_eq_product F hF)
  rw [hfun]
  have hpt : (2 : ℂ) ^ m * (ℓ : ℂ) = (((2 ^ m * ℓ : ℤ) : ℤ) : ℂ) := by
    push_cast
    ring
  rw [hpt]
  refine iteratedDeriv_rvachevFourierProduct_int_eq_zero_of_lt
    (2 ^ m * ℓ) (mul_ne_zero (pow_ne_zero m two_ne_zero) hℓ) ?_
  have habs : (2 ^ m * ℓ : ℤ).natAbs = 2 ^ m * ℓ.natAbs := by
    rw [Int.natAbs_mul]
    congr 1
    simp
  rw [habs]
  have hval : padicValNat 2 (2 ^ m * ℓ.natAbs) =
      m + padicValNat 2 ℓ.natAbs := by
    rw [padicValNat.mul (pow_ne_zero m two_ne_zero)
      (Int.natAbs_ne_zero.mpr hℓ), padicValNat.prime_pow]
  omega

/-- **Alias vanishing**: the Fourier transform of `x^p·up(2^{-m}·x)`
vanishes at every nonzero integer frequency, for `p ≤ m`. -/
theorem fourier_monomialRvachevSchwartz_int_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) {p : ℕ}
    (hp : p ≤ m) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    𝓕 (⇑(monomialRvachevSchwartz F hF p ((2 : ℝ) ^ m)⁻¹
      (by positivity))) (ℓ : ℝ) = 0 := by
  have hu : (0 : ℝ) < ((2 : ℝ) ^ m)⁻¹ := by positivity
  have hne : ((2 : ℝ) ^ m)⁻¹ ≠ 0 := hu.ne'
  have hkey := fourier_monomialRvachevSchwartz F hF p hne (ℓ : ℝ)
  rw [iteratedDeriv_fourier_scaledRvachevSchwartz F hF hu p (ℓ : ℝ)]
    at hkey
  have hpt : ((((ℓ : ℝ) / ((2 : ℝ) ^ m)⁻¹ : ℝ)) : ℂ) =
      (2 : ℂ) ^ m * (ℓ : ℂ) := by
    rw [div_inv_eq]
    push_cast
    ring
  rw [hpt, iteratedDeriv_rvachevFourier_two_pow_int_eq_zero F hF m hℓ hp,
    smul_zero, smul_zero] at hkey
  have hcoeff : ((-(2 * (Real.pi : ℂ) * Complex.I)) ^ p : ℂ) ≠ 0 := by
    apply pow_ne_zero
    simp only [neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have := smul_eq_zero.mp hkey
  rcases this with h | h
  · exact absurd h hcoeff
  · exact h

end Fabius

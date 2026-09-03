import FabiusFunction.MonomialCombDerivatives
import FabiusFunction.IntegerZeroAnalyticOrder

/-!
# Alias vanishing for the monomial combs

Stage three (first half) of the shifted exactness theorem: at the
scale `u = 1/M` of an arbitrary integer mesh `M ≥ 1`, every
nonzero-frequency alias of the monomial sample function vanishes for
`p ≤ v₂(M)`.  Only the two-adic valuation of the mesh matters; the
dyadic mesh `M = 2^m` (where `v₂(M) = m`) is the instance the rest of
the arc uses.

* `iteratedDeriv_rvachevFourier_nat_mul_int_eq_zero` — the complex
  derivatives of the transform of order `p ≤ v₂(M)` vanish at `M·ℓ`
  (`ℓ ≠ 0`): the integer-zero order there is `v₂(Mℓ)+1 ≥ v₂(M)+1`.
* `fourier_monomialRvachevSchwartz_nat_int_eq_zero` — hence the Fourier
  transform of `x^p·up(x/M)` vanishes at every nonzero integer
  frequency: through the identities of stages one and two, that
  transform is a nonzero multiple of the vanishing derivative.
* `iteratedDeriv_rvachevFourier_two_pow_int_eq_zero`,
  `fourier_monomialRvachevSchwartz_int_eq_zero` — the dyadic instances
  `M = 2^m`.

The second half assembles Poisson summation: with all nonzero
aliases gone, the shifted comb sum equals the zero-frequency term,
the integral.
-/

set_option autoImplicit false

open MeasureTheory Real Complex
open scoped ContDiff FourierTransform SchwartzMap

namespace Fabius

/-- Derivatives of order `p ≤ v₂(M)` of the analytic transform vanish
at the nonzero integer multiples of the mesh `M`. -/
theorem iteratedDeriv_rvachevFourier_nat_mul_int_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) {ℓ : ℤ}
    (hℓ : ℓ ≠ 0) {p : ℕ} (hp : p ≤ padicValNat 2 M) :
    iteratedDeriv p (rvachevFourier F) ((M : ℂ) * (ℓ : ℂ)) = 0 := by
  have hfun : rvachevFourier F = rvachevFourierProduct :=
    funext (rvachevFourier_eq_product F hF)
  rw [hfun]
  have hpt : (M : ℂ) * (ℓ : ℂ) = ((((M : ℤ) * ℓ : ℤ) : ℤ) : ℂ) := by
    push_cast
    ring
  rw [hpt]
  refine iteratedDeriv_rvachevFourierProduct_int_eq_zero_of_lt
    ((M : ℤ) * ℓ) (mul_ne_zero (Int.natCast_ne_zero.mpr hM) hℓ) ?_
  have habs : ((M : ℤ) * ℓ).natAbs = M * ℓ.natAbs := by
    rw [Int.natAbs_mul]
    simp
  rw [habs]
  have hval : padicValNat 2 (M * ℓ.natAbs) =
      padicValNat 2 M + padicValNat 2 ℓ.natAbs :=
    padicValNat.mul hM (Int.natAbs_ne_zero.mpr hℓ)
  omega

/-- Derivatives of order `p ≤ m` of the analytic transform vanish at
the nonzero multiples of `2^m`: the mesh `M = 2^m` has `v₂(M) = m`. -/
theorem iteratedDeriv_rvachevFourier_two_pow_int_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) {ℓ : ℤ}
    (hℓ : ℓ ≠ 0) {p : ℕ} (hp : p ≤ m) :
    iteratedDeriv p (rvachevFourier F) ((2 : ℂ) ^ m * (ℓ : ℂ)) = 0 := by
  have h := iteratedDeriv_rvachevFourier_nat_mul_int_eq_zero F hF
    (M := 2 ^ m) (pow_ne_zero m two_ne_zero) hℓ (p := p)
    (by rw [padicValNat.prime_pow]; exact hp)
  push_cast at h
  exact h

/-- **Alias vanishing on integer meshes**: the Fourier transform of
`x^p·up(x/M)` vanishes at every nonzero integer frequency, for
`p ≤ v₂(M)`. -/
theorem fourier_monomialRvachevSchwartz_nat_int_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) {p : ℕ}
    (hp : p ≤ padicValNat 2 M) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    𝓕 (⇑(monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
      (inv_ne_zero (Nat.cast_ne_zero.mpr hM)))) (ℓ : ℝ) = 0 := by
  have hu : (0 : ℝ) < ((M : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM))
  have hne : ((M : ℝ))⁻¹ ≠ 0 := hu.ne'
  have hkey := fourier_monomialRvachevSchwartz F hF p hne (ℓ : ℝ)
  rw [iteratedDeriv_fourier_scaledRvachevSchwartz F hF hu p (ℓ : ℝ)]
    at hkey
  have hpt : ((((ℓ : ℝ) / ((M : ℝ))⁻¹ : ℝ)) : ℂ) =
      (M : ℂ) * (ℓ : ℂ) := by
    rw [division_def, inv_inv]
    push_cast
    ring
  rw [hpt, iteratedDeriv_rvachevFourier_nat_mul_int_eq_zero F hF hM hℓ
    hp, smul_zero, smul_zero] at hkey
  have hcoeff : ((-(2 * (Real.pi : ℂ) * Complex.I)) ^ p : ℂ) ≠ 0 := by
    apply pow_ne_zero
    simp only [neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have := smul_eq_zero.mp hkey
  rcases this with h | h
  · exact absurd h hcoeff
  · exact h

/-- **Alias vanishing, dyadic instance**: the Fourier transform of
`x^p·up(2^{-m}·x)` vanishes at every nonzero integer frequency, for
`p ≤ m`. -/
theorem fourier_monomialRvachevSchwartz_int_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) {p : ℕ}
    (hp : p ≤ m) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    𝓕 (⇑(monomialRvachevSchwartz F hF p ((2 : ℝ) ^ m)⁻¹
      (by positivity))) (ℓ : ℝ) = 0 := by
  have h := fourier_monomialRvachevSchwartz_nat_int_eq_zero F hF
    (M := 2 ^ m) (pow_ne_zero m two_ne_zero) (p := p)
    (by rw [padicValNat.prime_pow]; exact hp) hℓ
  push_cast at h
  exact h

end Fabius

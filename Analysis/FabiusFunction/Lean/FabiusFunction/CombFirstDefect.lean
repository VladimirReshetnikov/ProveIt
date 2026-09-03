import FabiusFunction.CompositeMeshExactness

/-!
# The first defect: sharpness of the two-adic exactness threshold

`CompositeMeshExactness` proves that the mesh-`M` comb integrates
every polynomial of degree `≤ v₂(M)` exactly.  This module proves the
threshold *sharp*: one degree higher, at `p = v₂(M)+1`, the first
Poisson alias survives.

* `iteratedDeriv_rvachevFourierProduct_nat_mul_int_of_odd` — at an
  odd multiple `M·ℓ` of the mesh, the `p`-th derivative of the
  analytic transform takes the exact nonzero value
  `-p!·Û(q/2)/(Mℓ)^p`, where `q` is the odd part of `Mℓ`: these are
  the `Φ(qℓ/2)`-values that the comb volume's first-defect data
  tabulates;
* `fourier_monomialRvachevSchwartz_nat_int_ne_zero_of_odd` — hence
  the Fourier transform of `x^p·up(x/M)` does **not** vanish at odd
  integer frequencies: the quadrature/reproduction order of the mesh
  is exactly `v₂(M)`, not more.
-/

set_option autoImplicit false

open MeasureTheory Real Complex
open scoped ContDiff FourierTransform SchwartzMap

namespace Fabius

/-- At an odd multiple of the mesh the `(v₂(M)+1)`-st derivative of
the sinc product takes its exact first-defect value. -/
theorem iteratedDeriv_rvachevFourierProduct_nat_mul_int_of_odd
    {M : ℕ} (hM : M ≠ 0) {ℓ : ℤ} (hℓ : Odd ℓ) :
    iteratedDeriv (padicValNat 2 M + 1) rvachevFourierProduct
        ((M : ℂ) * (ℓ : ℂ)) =
      -(((padicValNat 2 M + 1).factorial : ℂ)) *
          rvachevFourierProduct
            (((Nat.divMaxPow ((M : ℤ) * ℓ).natAbs 2 : ℕ) : ℂ) / 2) /
        ((M : ℂ) * (ℓ : ℂ)) ^ (padicValNat 2 M + 1) := by
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hℓ
    omega
  have hm0 : (M : ℤ) * ℓ ≠ 0 :=
    mul_ne_zero (Int.natCast_ne_zero.mpr hM) hℓ0
  have hval : padicValNat 2 ((M : ℤ) * ℓ).natAbs = padicValNat 2 M := by
    have habs : ((M : ℤ) * ℓ).natAbs = M * ℓ.natAbs := by
      rw [Int.natAbs_mul]
      simp
    have hodd : padicValNat 2 ℓ.natAbs = 0 := by
      refine padicValNat.eq_zero_of_not_dvd ?_
      have h1 : ℓ.natAbs % 2 = 1 :=
        Nat.odd_iff.mp (Int.natAbs_odd.mpr hℓ)
      omega
    rw [habs, padicValNat.mul hM (Int.natAbs_ne_zero.mpr hℓ0), hodd]
    omega
  have h := iteratedDeriv_rvachevFourierProduct_int ((M : ℤ) * ℓ) hm0
  rw [hval] at h
  have hpt : ((((M : ℤ) * ℓ : ℤ)) : ℂ) = (M : ℂ) * (ℓ : ℂ) := by
    push_cast
    ring
  rw [hpt] at h
  exact h

/-- **Sharpness of the two-adic threshold**: at degree
`p = v₂(M)+1` the transform of the monomial sample function does not
vanish at odd frequencies — the first alias survives, so the
composite-mesh exactness degree `v₂(M)` cannot be improved. -/
theorem fourier_monomialRvachevSchwartz_nat_int_ne_zero_of_odd
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    {ℓ : ℤ} (hℓ : Odd ℓ) :
    𝓕 (⇑(monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
        ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))))
      (ℓ : ℝ) ≠ 0 := by
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hℓ
    omega
  have hu : (0 : ℝ) < ((M : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM))
  have hne : ((M : ℝ))⁻¹ ≠ 0 := hu.ne'
  intro h0
  have hkey := fourier_monomialRvachevSchwartz F hF
    (padicValNat 2 M + 1) hne (ℓ : ℝ)
  rw [iteratedDeriv_fourier_scaledRvachevSchwartz F hF hu
    (padicValNat 2 M + 1) (ℓ : ℝ)] at hkey
  have hpt : ((((ℓ : ℝ) / ((M : ℝ))⁻¹ : ℝ)) : ℂ) =
      (M : ℂ) * (ℓ : ℂ) := by
    rw [division_def, inv_inv]
    push_cast
    ring
  rw [hpt, h0, smul_zero] at hkey
  have hfun : rvachevFourier F = rvachevFourierProduct :=
    funext (rvachevFourier_eq_product F hF)
  rw [hfun] at hkey
  have hD_ne : iteratedDeriv (padicValNat 2 M + 1)
      rvachevFourierProduct ((M : ℂ) * (ℓ : ℂ)) ≠ 0 := by
    rw [iteratedDeriv_rvachevFourierProduct_nat_mul_int_of_odd hM hℓ]
    have habs0 : ((M : ℤ) * ℓ).natAbs ≠ 0 :=
      Int.natAbs_ne_zero.mpr
        (mul_ne_zero (Int.natCast_ne_zero.mpr hM) hℓ0)
    have hqodd : Odd (Nat.divMaxPow ((M : ℤ) * ℓ).natAbs 2) :=
      Nat.not_even_iff_odd.mp
        (mt Even.two_dvd
          (Nat.not_dvd_divMaxPow (by norm_num) habs0))
    refine div_ne_zero (mul_ne_zero (neg_ne_zero.mpr ?_) ?_)
      (pow_ne_zero _ ?_)
    · exact_mod_cast Nat.factorial_ne_zero _
    · exact rvachevFourierProduct_nat_div_two_ne_zero_of_odd hqodd
    · exact mul_ne_zero (Nat.cast_ne_zero.mpr hM)
        (Int.cast_ne_zero.mpr hℓ0)
  have hu_ne : ((((M : ℝ))⁻¹)⁻¹ : ℝ) ≠ 0 := by
    rw [inv_inv]
    exact Nat.cast_ne_zero.mpr hM
  rcases smul_eq_zero.mp hkey.symm with h | h
  · exact hu_ne h
  rcases smul_eq_zero.mp h with h' | h'
  · exact pow_ne_zero _ hu_ne h'
  · exact hD_ne h'

/-- Sharp valuation form of the alias vanishing: the `p`-th
derivative dies at `M·ℓ` whenever `p ≤ v₂(M) + v₂(ℓ)` — the mesh and
the frequency contribute their two-adic valuations jointly. -/
theorem iteratedDeriv_rvachevFourier_nat_mul_int_eq_zero_of_le
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) {p : ℕ}
    (hp : p ≤ padicValNat 2 M + padicValNat 2 ℓ.natAbs) :
    iteratedDeriv p (rvachevFourier F) ((M : ℂ) * (ℓ : ℂ)) = 0 := by
  have hfun : rvachevFourier F = rvachevFourierProduct :=
    funext (rvachevFourier_eq_product F hF)
  rw [hfun]
  have hpt : (M : ℂ) * (ℓ : ℂ) = ((((M : ℤ) * ℓ : ℤ)) : ℂ) := by
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

/-- Sharp valuation form of the transform vanishing. -/
theorem fourier_monomialRvachevSchwartz_nat_int_eq_zero_of_le
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    {p : ℕ} {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    (hp : p ≤ padicValNat 2 M + padicValNat 2 ℓ.natAbs) :
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
  rw [hpt, iteratedDeriv_rvachevFourier_nat_mul_int_eq_zero_of_le
    F hF hM hℓ hp, smul_zero, smul_zero] at hkey
  have hcoeff : ((-(2 * (Real.pi : ℂ) * Complex.I)) ^ p : ℂ) ≠ 0 := by
    apply pow_ne_zero
    simp only [neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  rcases smul_eq_zero.mp hkey with h | h
  · exact absurd h hcoeff
  · exact h

/-- The zero-frequency Fourier coefficient of the comb is the
integral. -/
theorem fourier_monomialRvachevSchwartz_nat_zero (F : BoundedFabius)
    (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) (p : ℕ) :
    𝓕 (⇑(monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
        (inv_ne_zero (Nat.cast_ne_zero.mpr hM)))) (0 : ℝ) =
      ∫ x : ℝ, ((x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  simp [monomialRvachevSchwartz_apply]

/-- **The spectral display**: the shifted monomial comb *is* its
Fourier series, at every degree, mesh, and shift.  Combined with the
coefficient trichotomy — the zero frequency carries the integral
(`fourier_monomialRvachevSchwartz_nat_zero`), frequencies with
`p ≤ v₂(M) + v₂(ℓ)` vanish
(`fourier_monomialRvachevSchwartz_nat_int_eq_zero_of_le`), and at the
threshold degree the odd frequencies survive with exact values
(`fourier_monomialRvachevSchwartz_nat_int_ne_zero_of_odd`) — this is
the comb's complete spectral resolution. -/
theorem tsum_shifted_monomial_eq_tsum_fourier (F : BoundedFabius)
    (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) (p : ℕ) (θ : ℝ) :
    ∑' k : ℤ, monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
        (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) (θ + k) =
      ∑' ℓ : ℤ, 𝓕 (monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
          (inv_ne_zero (Nat.cast_ne_zero.mpr hM))) ℓ *
        fourier ℓ (θ : UnitAddCircle) :=
  SchwartzMap.tsum_eq_tsum_fourier _ θ

end Fabius

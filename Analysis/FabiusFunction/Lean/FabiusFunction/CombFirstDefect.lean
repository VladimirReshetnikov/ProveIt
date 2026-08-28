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

end Fabius

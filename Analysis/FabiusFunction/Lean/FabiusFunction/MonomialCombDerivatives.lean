import FabiusFunction.MonomialCombFourier
import FabiusFunction.FourierAnalytic
import FabiusFunction.NegativeLaplaceVerticalAllOrderBound

/-!
# Derivatives of the scaled Rvachev Fourier transform

Stage two of the shifted dyadic exactness theorem: the derivative
side of `fourier_monomialRvachevSchwartz` is evaluated through the
analytic transform.

* `fourier_coe_scaledRvachevSchwartz` — the function-level transform
  of the scaled sample function, `𝓕(up(u·)) = u⁻¹·Û(·/u)`;
* `contDiff_rvachevFourier_ofReal` — the real-axis restriction of
  the entire transform is smooth;
* `iteratedDeriv_fourier_scaledRvachevSchwartz` — the derivatives:
  `(𝓕(up(u·)))⁽ᵖ⁾(w) = u⁻¹·u⁻ᵖ·Û⁽ᵖ⁾(w/u)`, with `Û⁽ᵖ⁾` the complex
  iterated derivative of the entire transform, transported to the
  real axis by the corpus's real–complex derivative bridge
  (`iteratedDeriv_comp_ofReal_eq_of_differentiableOn`).

Stage three specializes `w` to nonzero integers at `u = 2^{-m}`,
where `Û⁽ᵖ⁾(2^m ℓ) = 0` for `p ≤ m` by the integer-zero order
theorem, and assembles Poisson summation into the exactness
statement.
-/

set_option autoImplicit false

open MeasureTheory Real Complex
open scoped ContDiff FourierTransform SchwartzMap

namespace Fabius

/-- The function-level Fourier transform of the scaled sample
function: `𝓕(up(u·)) = u⁻¹·Û(·/u)`. -/
theorem fourier_coe_scaledRvachevSchwartz (F : BoundedFabius)
    (hF : IsFabius F) {u : ℝ} (hu : 0 < u) :
    𝓕 (⇑(scaledRvachevSchwartz F hF u hu.ne')) =
      fun w : ℝ => (u⁻¹ : ℝ) • rvachevFourier F (((w / u : ℝ) : ℂ)) :=
  funext fun w => fourier_scaledRvachevSchwartz F hF hu w

/-- The restriction of the analytic transform to the real axis is
smooth. -/
theorem contDiff_rvachevFourier_ofReal (F : BoundedFabius)
    (hF : IsFabius F) {n : ℕ∞} :
    ContDiff ℝ n (fun t : ℝ => rvachevFourier F (t : ℂ)) := by
  have hG : ContDiff ℂ n (rvachevFourier F) :=
    (rvachevFourier_differentiable_analytic F hF).contDiff
  exact (hG.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff

/-- **Derivatives of the scaled transform**:
`(𝓕(up(u·)))⁽ᵖ⁾(w) = u⁻¹·u⁻ᵖ·Û⁽ᵖ⁾(w/u)` with the complex iterated
derivative of the entire transform on the right. -/
theorem iteratedDeriv_fourier_scaledRvachevSchwartz
    (F : BoundedFabius) (hF : IsFabius F) {u : ℝ} (hu : 0 < u)
    (p : ℕ) (w : ℝ) :
    iteratedDeriv p (𝓕 (⇑(scaledRvachevSchwartz F hF u hu.ne'))) w =
      (u⁻¹ : ℝ) • ((u⁻¹ : ℝ) ^ p •
        iteratedDeriv p (rvachevFourier F) (((w / u : ℝ) : ℂ))) := by
  rw [fourier_coe_scaledRvachevSchwartz F hF hu]
  have hshape : (fun w : ℝ =>
      (u⁻¹ : ℝ) • rvachevFourier F (((w / u : ℝ) : ℂ))) =
      (u⁻¹ : ℝ) • (fun w : ℝ =>
        (fun t : ℝ => rvachevFourier F (t : ℂ)) (u⁻¹ * w)) := by
    funext v
    simp only [Pi.smul_apply]
    show (u⁻¹ : ℝ) • rvachevFourier F (((v / u : ℝ) : ℂ)) =
      (u⁻¹ : ℝ) • rvachevFourier F (((u⁻¹ * v : ℝ) : ℂ))
    rw [inv_mul_eq_div]
  rw [hshape]
  have hcd : ContDiffAt ℝ (p : ℕ∞) (fun w : ℝ =>
      (fun t : ℝ => rvachevFourier F (t : ℂ)) (u⁻¹ * w)) w :=
    (((contDiff_rvachevFourier_ofReal F hF (n := (p : ℕ∞))).comp
      (contDiff_const.smul contDiff_id)).contDiffAt)
  rw [iteratedDeriv_const_smul hcd (u⁻¹ : ℝ)]
  simp only [Pi.smul_apply]
  congr 1
  have hg : ContDiff ℝ (p : ℕ∞)
      (fun t : ℝ => rvachevFourier F (t : ℂ)) :=
    contDiff_rvachevFourier_ofReal F hF
  rw [iteratedDeriv_comp_const_smul hg (u⁻¹ : ℝ)]
  show (u⁻¹ : ℝ) ^ p • iteratedDeriv p
      (fun t : ℝ => rvachevFourier F (t : ℂ)) (u⁻¹ * w) =
    (u⁻¹ : ℝ) ^ p •
      iteratedDeriv p (rvachevFourier F) (((w / u : ℝ) : ℂ))
  congr 1
  rw [iteratedDeriv_comp_ofReal_eq_of_differentiableOn
    (rvachevFourier F) isOpen_univ
    (rvachevFourier_differentiable_analytic F hF).differentiableOn
    p (u⁻¹ * w) (Set.mem_univ _), inv_mul_eq_div]

end Fabius

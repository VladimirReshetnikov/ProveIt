import FabiusFunction.MonomialCombFourier
import FabiusFunction.FourierAnalytic

/-!
# Derivatives of the scaled Rvachev Fourier transform

Stage two of the shifted dyadic exactness theorem: the derivative
side of `fourier_monomialRvachevSchwartz` is evaluated through the
analytic transform.

* `iteratedDeriv_comp_ofReal` — **the real–complex derivative
  bridge**: real iterated derivatives of the restriction of an entire
  function are the restrictions of its complex iterated derivatives.
* `fourier_coe_scaledRvachevSchwartz` — the function-level transform
  of the scaled sample function, `𝓕(up(u·)) = u⁻¹·Û(·/u)`.
* `iteratedDeriv_fourier_scaledRvachevSchwartz` — its derivatives:
  `(𝓕(up(u·)))⁽ᵖ⁾(w) = u⁻¹·u⁻ᵖ·Û⁽ᵖ⁾(w/u)`, with `Û⁽ᵖ⁾` the complex
  iterated derivative of the entire transform.

Stage three specializes `w` to nonzero integers at `u = 2^{-m}`,
where `Û⁽ᵖ⁾(2^m ℓ) = 0` for `p ≤ m` by the integer-zero order
theorem, and assembles Poisson summation into the exactness
statement.
-/

set_option autoImplicit false

open MeasureTheory Real Complex
open scoped ContDiff FourierTransform SchwartzMap

namespace Fabius

/-- **The real–complex iterated-derivative bridge**: for an entire
function, the real iterated derivatives of its restriction to `ℝ` are
the restrictions of its complex iterated derivatives. -/
theorem iteratedDeriv_comp_ofReal {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun y : ℝ => G (y : ℂ)) t =
      iteratedDeriv n G (t : ℂ) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
      have hGn : Differentiable ℂ (iteratedDeriv n G) :=
        (hG.contDiff (n := (⊤ : ℕ∞))).differentiable_iteratedDeriv
          (by exact_mod_cast lt_top_iff_ne_top.mpr (by simp))
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hfun : iteratedDeriv n (fun y : ℝ => G (y : ℂ)) =
          fun y : ℝ => iteratedDeriv n G (y : ℂ) :=
        funext fun y => ih y
      rw [hfun]
      exact ((hGn ((t : ℝ) : ℂ)).hasDerivAt.comp_ofReal).deriv

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
      fun w : ℝ => (u⁻¹ : ℝ) •
        (fun t : ℝ => rvachevFourier F (t : ℂ)) (u⁻¹ • w) := by
    funext v
    simp only [smul_eq_mul]
    rw [inv_mul_eq_div]
  rw [hshape]
  rw [iteratedDeriv_const_smul
    (((contDiff_rvachevFourier_ofReal F hF (n := (p : ℕ∞))).comp
      (contDiff_const.smul contDiff_id)).contDiffAt) (u⁻¹ : ℝ)]
  congr 1
  rw [iteratedDeriv_comp_const_smul
    (contDiff_rvachevFourier_ofReal F hF (n := (p : ℕ∞))) (u⁻¹ : ℝ)]
  simp only [smul_eq_mul]
  rw [iteratedDeriv_comp_ofReal
    (rvachevFourier_differentiable_analytic F hF) p (u⁻¹ * w),
    inv_mul_eq_div]

end Fabius

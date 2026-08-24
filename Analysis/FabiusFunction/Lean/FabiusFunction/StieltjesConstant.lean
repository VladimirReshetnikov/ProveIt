import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The first Stieltjes constant

This file fixes the sign convention for the first Stieltjes constant and records the local
Taylor/Laurent expansion of the Riemann zeta function at its pole.
-/

set_option autoImplicit false

open Filter Asymptotics
open scoped Topology

namespace Fabius

/-- The real restriction of the entire regular part of the Riemann zeta function at `1`. -/
noncomputable def zetaRegularReal (x : ℝ) : ℝ :=
  (riemannZeta₀ (x : ℂ)).re

/-- The first Stieltjes constant, with the convention
`ζ(1+s) = s⁻¹ + γ - γ₁ s + O(s²)`. -/
noncomputable def firstStieltjesConstant : ℝ :=
  -deriv zetaRegularReal 1

theorem differentiable_zetaRegularReal : Differentiable ℝ zetaRegularReal := by
  unfold zetaRegularReal
  fun_prop

theorem contDiff_zetaRegularReal {n : WithTop ℕ∞} : ContDiff ℝ n zetaRegularReal := by
  exact differentiable_riemannZeta₀.contDiff.real_of_complex

theorem zetaRegularReal_hasDerivAt (x : ℝ) :
    HasDerivAt zetaRegularReal (deriv riemannZeta₀ (x : ℂ)).re x := by
  exact differentiable_riemannZeta₀.differentiableAt.hasDerivAt.real_of_complex

theorem deriv_zetaRegularReal (x : ℝ) :
    deriv zetaRegularReal x = (deriv riemannZeta₀ (x : ℂ)).re :=
  (zetaRegularReal_hasDerivAt x).deriv

@[simp] theorem zetaRegularReal_one :
    zetaRegularReal 1 = Real.eulerMascheroniConstant := by
  simp [zetaRegularReal]

theorem firstStieltjesConstant_eq_neg_re_deriv :
    firstStieltjesConstant = -(deriv riemannZeta₀ 1).re := by
  rw [firstStieltjesConstant, deriv_zetaRegularReal]
  norm_num

lemma riemannZeta₀_ofReal_eq_ofReal_re (x : ℝ) :
    riemannZeta₀ (x : ℂ) = (zetaRegularReal x : ℂ) := by
  apply Complex.ext
  · simp [zetaRegularReal]
  · rw [Complex.ofReal_im]
    rw [← Complex.conj_eq_iff_im]
    unfold riemannZeta₀
    split_ifs with hx
    · simp
    · rw [map_sub, ← riemannZeta_conj]
      simp

theorem deriv_riemannZeta₀_ofReal (x : ℝ) :
    deriv riemannZeta₀ (x : ℂ) = ((deriv zetaRegularReal x : ℝ) : ℂ) := by
  have hc : HasDerivAt (fun y : ℝ ↦ riemannZeta₀ (y : ℂ))
      (deriv riemannZeta₀ (x : ℂ)) x :=
    differentiable_riemannZeta₀.differentiableAt.hasDerivAt.comp_ofReal
  have hr : HasDerivAt (fun y : ℝ ↦ (zetaRegularReal y : ℂ))
      ((deriv zetaRegularReal x : ℝ) : ℂ) x :=
    (differentiable_zetaRegularReal x).hasDerivAt.ofReal_comp
  have hr' : HasDerivAt (fun y : ℝ ↦ riemannZeta₀ (y : ℂ))
      ((deriv zetaRegularReal x : ℝ) : ℂ) x :=
    hr.congr_of_eventuallyEq
      (Filter.Eventually.of_forall riemannZeta₀_ofReal_eq_ofReal_re)
  exact hc.unique hr'

theorem deriv_riemannZeta₀_one :
    deriv riemannZeta₀ 1 = -(firstStieltjesConstant : ℂ) := by
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, deriv_riemannZeta₀_ofReal]
  simp [firstStieltjesConstant]

theorem riemannZeta₀_hasDerivAt_one :
    HasDerivAt riemannZeta₀ (-(firstStieltjesConstant : ℂ)) 1 := by
  simpa [deriv_riemannZeta₀_one] using
    (differentiable_riemannZeta₀.differentiableAt.hasDerivAt :
      HasDerivAt riemannZeta₀ (deriv riemannZeta₀ 1) 1)

/-- First-order Taylor expansion of the entire regular part of zeta at `1`.

The sign is chosen so that the coefficient of `s` is `-γ₁`. -/
theorem riemannZeta₀_taylor_first :
    (fun s : ℂ ↦ riemannZeta₀ (1 + s) - Real.eulerMascheroniConstant +
        (firstStieltjesConstant : ℂ) * s) =o[𝓝 0] (fun s : ℂ ↦ s) := by
  have h := (hasDerivAt_iff_isLittleO_nhds_zero.mp riemannZeta₀_hasDerivAt_one)
  simpa [mul_comm] using h

/-- Laurent expansion of zeta at `1`, through its linear regular term. -/
theorem riemannZeta_laurent_first :
    (fun s : ℂ ↦ riemannZeta (1 + s) - s⁻¹ - Real.eulerMascheroniConstant +
        (firstStieltjesConstant : ℂ) * s) =o[𝓝[≠] 0] (fun s : ℂ ↦ s) := by
  refine (riemannZeta₀_taylor_first.mono nhdsWithin_le_nhds).congr' ?_
    (Filter.Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := by simpa using hs
  rw [riemannZeta_eq_inv_sub_add (by simpa using hs0)]
  ring_nf

/-- Second-order Taylor expansion after regularizing the pole of zeta.

Equivalently, `s * ζ(1+s) = 1 + γs - γ₁s² + o(s²)` on a punctured neighborhood of
zero. This form is convenient when multiplying by the corresponding regularization of `Γ(s)`. -/
theorem mul_riemannZeta_one_add_taylor_second :
    (fun s : ℂ ↦ s * riemannZeta (1 + s) -
        (1 + Real.eulerMascheroniConstant * s -
          (firstStieltjesConstant : ℂ) * s ^ 2)) =o[𝓝[≠] 0]
      (fun s : ℂ ↦ s ^ 2) := by
  have hTaylor :
      (fun s : ℂ ↦ riemannZeta₀ (1 + s) - Real.eulerMascheroniConstant +
          (firstStieltjesConstant : ℂ) * s) =o[𝓝[≠] 0] (fun s : ℂ ↦ s) :=
    riemannZeta₀_taylor_first.mono nhdsWithin_le_nhds
  have hmul := (isBigO_refl (fun s : ℂ ↦ s) (𝓝[≠] 0)).mul_isLittleO hTaylor
  refine hmul.congr' ?_ (Filter.Eventually.of_forall fun s ↦ by ring)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := by simpa using hs
  rw [riemannZeta_eq_inv_sub_add (by simpa using hs0)]
  rw [show 1 + s - 1 = s by ring]
  simp only [mul_add]
  rw [mul_inv_cancel₀ hs0]
  ring

/-- The Euler--Stieltjes combination occurring (with the opposite sign) as the constant
coefficient in the Laurent expansion of `Γ(s) * ζ(1+s)`. -/
noncomputable def gammaZetaConstant : ℝ :=
  Real.eulerMascheroniConstant ^ 2 / 2 + firstStieltjesConstant - Real.pi ^ 2 / 12

theorem gammaZetaConstant_eq_div_twelve :
    gammaZetaConstant =
      (6 * Real.eulerMascheroniConstant ^ 2 + 12 * firstStieltjesConstant -
        Real.pi ^ 2) / 12 := by
  unfold gammaZetaConstant
  ring

end Fabius

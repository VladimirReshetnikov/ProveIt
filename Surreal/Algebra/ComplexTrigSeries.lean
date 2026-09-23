import Surreal.Algebra.AnalyticComposition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Complex trigonometric Taylor germs

The actual Taylor series of ordinary complex sine and cosine at zero
satisfy the formal identities used in `trigonometry:thm:fold` and
`trigonometry:eq:foldroots`. Every substitution has zero constant
coefficient. Ordinary analytic germ identities are transported through
the proved Taylor addition, multiplication and composition rules.
Evaluation on infinitesimal surcomplex inputs is treated separately.
-/

namespace Surreal.Analytic

noncomputable section

/-- The formal Taylor germ of ordinary complex sine at zero. -/
def complexSinSeries : PowerSeries ℂ := taylorSeries Complex.sin 0

/-- The formal Taylor germ of ordinary complex cosine at zero. -/
def complexCosSeries : PowerSeries ℂ := taylorSeries Complex.cos 0

@[simp] theorem constantCoeff_complexSinSeries : complexSinSeries.constantCoeff = 0 := by
  simp [complexSinSeries]

@[simp] theorem constantCoeff_complexCosSeries : complexCosSeries.constantCoeff = 1 := by
  simp [complexCosSeries]

@[simp] theorem coeff_complexSinSeries_one : complexSinSeries.coeff 1 = 1 := by
  simp [complexSinSeries, coeff_taylorSeries, iteratedDeriv_succ, Complex.deriv_sin]

@[simp] theorem coeff_complexCosSeries_one : complexCosSeries.coeff 1 = 0 := by
  simp [complexCosSeries, coeff_taylorSeries, iteratedDeriv_succ, Complex.deriv_cos]

/-- The cosine germ has its nonzero quadratic coefficient before any evaluation. -/
@[simp] theorem coeff_complexCosSeries_two : complexCosSeries.coeff 2 = -(1 / 2 : ℂ) := by
  simp [complexCosSeries, coeff_taylorSeries, iteratedDeriv_succ,
    Complex.deriv_sin, neg_div]

/-- Formal differentiation gives the cosine germ. -/
theorem derivative_complexSinSeries : PowerSeries.derivative ℂ complexSinSeries =
    complexCosSeries := by
  rw [complexSinSeries, ← taylorSeries_deriv, Complex.deriv_sin]
  rfl

/-- Formal differentiation of cosine gives minus the sine germ. -/
theorem derivative_complexCosSeries : PowerSeries.derivative ℂ complexCosSeries =
    -complexSinSeries := by
  rw [complexCosSeries, ← taylorSeries_deriv,
    show deriv Complex.cos = -Complex.sin from funext (fun _ => Complex.deriv_cos), taylorSeries_neg]
  rfl

private theorem taylorSeries_sub_zero {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorSeries (f - g) 0 = taylorSeries f 0 - taylorSeries g 0 := by
  rw [sub_eq_add_neg, taylorSeries_add hf hg.neg, taylorSeries_neg, sub_eq_add_neg]

private theorem taylorSeries_comp_mul_zero (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (a : ℂ) :
    taylorSeries (fun z => f (a * z)) 0 =
      (taylorSeries f 0).subst (PowerSeries.C a * PowerSeries.X) := by
  have hg : taylorSeries ((fun _ : ℂ => a) * id) 0 =
      PowerSeries.C a * PowerSeries.X := by
    rw [taylorSeries_mul analyticAt_const analyticAt_id, taylorSeries_const, taylorSeries_id]
    simp
  have he := taylorSeries_comp (f := f) (g := (fun _ : ℂ => a) * id) (c := 0)
    (by simpa using hf) (analyticAt_const.mul analyticAt_id)
  simpa only [Function.comp_def, centeredTaylorSeries, hg, Pi.mul_apply,
    id_eq, mul_zero, map_zero, sub_zero] using he

/-- The formal complex germs satisfy the exact Pythagorean identity. -/
theorem complexSinSeries_sq_add_cos_sq : complexSinSeries ^ 2 + complexCosSeries ^ 2 = 1 := by
  have he : Complex.sin * Complex.sin + Complex.cos * Complex.cos = (fun _ : ℂ => 1) := by
    funext z
    simpa only [Pi.add_apply, Pi.mul_apply, pow_two] using Complex.sin_sq_add_cos_sq z
  have ht := congrArg (fun f : ℂ → ℂ => taylorSeries f 0) he
  rw [taylorSeries_add (Complex.analyticAt_sin.mul Complex.analyticAt_sin)
      (Complex.analyticAt_cos.mul Complex.analyticAt_cos),
    taylorSeries_mul Complex.analyticAt_sin Complex.analyticAt_sin,
    taylorSeries_mul Complex.analyticAt_cos Complex.analyticAt_cos, taylorSeries_const] at ht
  simpa only [complexSinSeries, complexCosSeries, pow_two, map_one] using ht

/-- Doubling the formal input gives the exact sine double-angle identity. -/
theorem complexSinSeries_subst_two_mul_X :
    complexSinSeries.subst (PowerSeries.C 2 * PowerSeries.X) =
      2 * complexSinSeries * complexCosSeries := by
  have he : (fun z : ℂ => Complex.sin (2 * z)) =
      ((fun _ : ℂ => 2) * Complex.sin) * Complex.cos := by
    funext z
    exact Complex.sin_two_mul z
  have ht := congrArg (fun f : ℂ → ℂ => taylorSeries f 0) he
  rw [taylorSeries_comp_mul_zero Complex.sin Complex.analyticAt_sin 2,
    taylorSeries_mul (analyticAt_const.mul Complex.analyticAt_sin) Complex.analyticAt_cos,
    taylorSeries_mul analyticAt_const Complex.analyticAt_sin, taylorSeries_const] at ht
  simpa only [complexSinSeries, complexCosSeries, map_ofNat] using ht

/-- The cosine fold is the formal identity `cos(2T)=1-2*sin(T)^2`. -/
theorem complexCosSeries_subst_two_mul_X :
    complexCosSeries.subst (PowerSeries.C 2 * PowerSeries.X) =
      1 - 2 * complexSinSeries ^ 2 := by
  have he : (fun z : ℂ => Complex.cos (2 * z)) =
      (fun _ : ℂ => 1) - (fun _ : ℂ => 2) * (Complex.sin * Complex.sin) := by
    funext z
    simpa only [Pi.sub_apply, Pi.mul_apply, pow_two] using Complex.cos_two_mul_eq_one_sub z
  have ht := congrArg (fun f : ℂ → ℂ => taylorSeries f 0) he
  rw [taylorSeries_comp_mul_zero Complex.cos Complex.analyticAt_cos 2,
    taylorSeries_sub_zero analyticAt_const
      (analyticAt_const.mul (Complex.analyticAt_sin.mul Complex.analyticAt_sin)),
    taylorSeries_mul analyticAt_const (Complex.analyticAt_sin.mul Complex.analyticAt_sin),
    taylorSeries_mul Complex.analyticAt_sin Complex.analyticAt_sin] at ht
  simpa only [complexSinSeries, complexCosSeries, taylorSeries_const, pow_two,
    map_one, map_ofNat] using ht

/-- The complex sine germ is odd as an identity of formally substituted series. -/
theorem complexSinSeries_subst_neg_X : complexSinSeries.subst (-PowerSeries.X) =
    -complexSinSeries := by
  have he : (fun z : ℂ => Complex.sin ((-1) * z)) = -Complex.sin := by
    funext z
    simp
  have ht := congrArg (fun f : ℂ → ℂ => taylorSeries f 0) he
  rw [taylorSeries_comp_mul_zero Complex.sin Complex.analyticAt_sin (-1), taylorSeries_neg] at ht
  simpa only [complexSinSeries, map_neg, map_one, neg_one_mul] using ht

/-- The complex cosine germ is even as an identity of formally substituted series. -/
theorem complexCosSeries_subst_neg_X : complexCosSeries.subst (-PowerSeries.X) =
    complexCosSeries := by
  have he : (fun z : ℂ => Complex.cos ((-1) * z)) = Complex.cos := by
    funext z
    simp
  have ht := congrArg (fun f : ℂ → ℂ => taylorSeries f 0) he
  rw [taylorSeries_comp_mul_zero Complex.cos Complex.analyticAt_cos (-1)] at ht
  simpa only [complexCosSeries, map_neg, map_one, neg_one_mul] using ht

end
end Surreal.Analytic

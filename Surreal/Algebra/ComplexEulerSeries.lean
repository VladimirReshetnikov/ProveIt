import Surreal.Algebra.ComplexTrigSeries
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The formal complex Euler identity

The ordinary analytic identity identifies the exponential coordinate used
for angular multiplicity with the previously constructed sine and cosine
germs. This supplies the formal coordinate in `trigonometry:thm:fold` and
the multiplicity argument of `trigonometry:thm:polyroots`.
-/

namespace Surreal.Analytic

noncomputable section

/-- Ordinary complex exponential has Mathlib's formal exponential as its Taylor series. -/
theorem taylorSeries_complex_exp_zero : taylorSeries Complex.exp 0 = PowerSeries.exp ℂ := by
  apply PowerSeries.exp_unique_of_derivative_eq_self
  · rw [← taylorSeries_deriv, Complex.deriv_exp]
  · simp

/-- Formal Euler identity with an admissible zero-constant substitution. -/
theorem complexEulerSeries :
    (PowerSeries.exp ℂ).subst (PowerSeries.C Complex.I * PowerSeries.X) =
      complexCosSeries + PowerSeries.C Complex.I * complexSinSeries := by
  have hg : taylorSeries ((fun _ : ℂ => Complex.I) * id) 0 =
      PowerSeries.C Complex.I * PowerSeries.X := by
    rw [taylorSeries_mul analyticAt_const analyticAt_id, taylorSeries_const, taylorSeries_id]
    simp
  have he : Complex.exp ∘ ((fun _ : ℂ => Complex.I) * id) =
      Complex.cos + (fun _ : ℂ => Complex.I) * Complex.sin := by
    funext z
    simpa only [Function.comp_apply, Pi.mul_apply, Pi.add_apply, id_eq, mul_comm] using
      (Complex.exp_mul_I (x := z))
  have hc := congrArg (fun f : ℂ → ℂ => taylorSeries f 0) he
  rw [taylorSeries_comp analyticAt_cexp (analyticAt_const.mul analyticAt_id),
    taylorSeries_add Complex.analyticAt_cos (analyticAt_const.mul Complex.analyticAt_sin),
    taylorSeries_mul analyticAt_const Complex.analyticAt_sin, taylorSeries_const] at hc
  simpa only [centeredTaylorSeries, hg, Pi.mul_apply, id_eq, mul_zero, map_zero, sub_zero,
    taylorSeries_complex_exp_zero, complexCosSeries, complexSinSeries] using hc

end
end Surreal.Analytic

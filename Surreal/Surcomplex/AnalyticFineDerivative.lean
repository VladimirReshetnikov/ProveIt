import Surreal.Surcomplex.AnalyticTaylor
import Surreal.Surcomplex.PowerSeriesFineDerivative

/-!
# Fine derivatives of Taylor lifts at ordinary centers

The translated formal Taylor evaluation is a total function, extended by zero
outside the center's infinitesimal monad. On that monad it agrees with the
explicit analytic Taylor evaluation and the correctly recentered finite lift.
At the ordinary center its fine derivative is the embedded ordinary derivative.
This is the ordinary-center case of `trigonometry:prop:lift`; differentiation
at nonordinary finite points remains separate.
-/

universe u

namespace Surreal.Surcomplex

noncomputable section

/-- Taylor evaluation translated to an ordinary center, with zero extension
outside its infinitesimal monad. -/
def analyticTaylorFunction (f : ℂ → ℂ) (c : ℂ) (z : Surcomplex.{u}) : Surcomplex.{u} :=
  powerSeriesFunction (Analytic.taylorSeries f c) (z - ofComplex c)

/-- On its monad the total function is the analytically witnessed Taylor lift. -/
theorem analyticTaylorFunction_of_isInfinitesimal (f : ℂ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℂ f c) (z : Surcomplex.{u})
    (hz : IsInfinitesimal (z - ofComplex c)) :
    analyticTaylorFunction f c z = analyticTaylorEvaluation f c hf (z - ofComplex c) hz := by
  exact powerSeriesFunction_of_isInfinitesimal _ _ hz

/-- The prescribed ordinary-center-plus-infinitesimal Taylor rule. -/
theorem analyticTaylorFunction_ofComplex_add (f : ℂ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℂ f c) (ε : Surcomplex.{u}) (hε : IsInfinitesimal ε) :
    analyticTaylorFunction f c (ofComplex c + ε) = analyticTaylorEvaluation f c hf ε hε := by
  simp only [analyticTaylorFunction, add_sub_cancel_left,
    powerSeriesFunction_of_isInfinitesimal _ _ hε, analyticTaylorEvaluation]

@[simp] theorem analyticTaylorFunction_ofComplex (f : ℂ → ℂ) (c : ℂ) :
    analyticTaylorFunction f c (ofComplex c : Surcomplex.{u}) = ofComplex (f c) := by
  simp [analyticTaylorFunction]

/-- The genuine ordinary analytic germ has the expected derivative for all fine tolerances. -/
theorem fineHasDerivAt_analyticTaylorFunction (f : ℂ → ℂ) (c : ℂ)
    (_hf : AnalyticAt ℂ f c) :
    FineHasDerivAt (analyticTaylorFunction f c) (ofComplex (deriv f c))
      (ofComplex c : Surcomplex.{u}) := by
  simpa only [FineHasDerivAt, analyticTaylorFunction, add_sub_cancel_left, sub_self,
    zero_add, Analytic.coeff_taylorSeries, iteratedDeriv_one, Nat.factorial_one,
    Nat.cast_one, div_one] using
    fineHasDerivAt_powerSeriesFunction_zero (Analytic.taylorSeries f c)

/-- The Taylor lift is continuous at the ordinary center in the actual fine topology. -/
theorem continuousAt_analyticTaylorFunction (f : ℂ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℂ f c) :
    ContinuousAt (analyticTaylorFunction f c) (ofComplex c : Surcomplex.{u}) :=
  (fineHasDerivAt_analyticTaylorFunction f c hf).continuousAt

/-- Agreement with the finite-input lift, retaining both its finite domain and
its explicit analytic standard-part witness. -/
theorem analyticTaylorFunction_standardPart_eq_analyticLift (f : ℂ → ℂ)
    (z : Surcomplex.{u}) (hz : IsFinite z) (hf : AnalyticAt ℂ f (standardPart z)) :
    analyticTaylorFunction f (standardPart z) z = analyticLift f z hz hf :=
  analyticTaylorFunction_of_isInfinitesimal f _ hf z (infinitesimal_sub_standardPart hz)

/-- An infinitesimal displacement has exactly the specified ordinary center,
so no evaluation at a different ordinary center occurs in this comparison. -/
theorem analyticTaylorFunction_eq_analyticLift_of_isInfinitesimal
    (f : ℂ → ℂ) (c : ℂ) (hf : AnalyticAt ℂ f c)
    (z : Surcomplex.{u}) (hz : IsFinite z) (hzc : IsInfinitesimal (z - ofComplex c)) :
    analyticTaylorFunction f c z = analyticLift f z hz
      (by rw [(infinitesimal_sub_ofComplex_iff hz).mp hzc]; exact hf) := by
  have hc : standardPart z = c := (infinitesimal_sub_ofComplex_iff hz).mp hzc
  subst c
  exact analyticTaylorFunction_standardPart_eq_analyticLift f z hz hf

end

end Surreal.Surcomplex

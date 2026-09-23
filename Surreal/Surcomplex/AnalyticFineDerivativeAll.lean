import Surreal.Algebra.FineDerivativeRules
import Surreal.Foundations.SignSequenceAnalyticTaylor
import Surreal.Surcomplex.AnalyticFineDerivative
import Surreal.Surcomplex.PowerSeriesDerivative

/-!
# Fine differentiation throughout an analytic monad

The fine derivative of a Taylor lift at any infinitesimal displacement is the
Taylor lift of the ordinary derivative at that same point. This proves the
nonordinary-center differentiation clause of `trigonometry:prop:lift`, for
both the actual surreal and surcomplex fields. The local function is centered
at the standard part of the finite point, as required by `found:rem:recentering`.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The real Taylor lift on a fixed ordinary monad, extended by zero outside it. -/
def analyticTaylorFunction (f : ℝ → ℝ) (c : ℝ) (z : SignSequence.{u}) : SignSequence.{u} :=
  powerSeriesFunction (Analytic.taylorSeries f c) (z - ofReal c)

/-- On the chosen monad this is the witnessed ordinary analytic Taylor evaluation. -/
theorem analyticTaylorFunction_of_isInfinitesimal (f : ℝ → ℝ) (c : ℝ)
    (hf : AnalyticAt ℝ f c) (z : SignSequence.{u}) (hz : IsInfinitesimal (z - ofReal c)) :
    analyticTaylorFunction f c z = analyticTaylorEvaluation f c hf (z - ofReal c) hz :=
  powerSeriesFunction_of_isInfinitesimal _ _ hz

/-- The ordinary center agrees with the original real value. -/
@[simp] theorem analyticTaylorFunction_ofReal (f : ℝ → ℝ) (c : ℝ) :
    analyticTaylorFunction f c (ofReal c : SignSequence.{u}) = ofReal (f c) := by
  simp [analyticTaylorFunction]

/-- The local function at the standard part represents the recentered finite lift. -/
theorem analyticTaylorFunction_standardPart_eq_analyticLift (f : ℝ → ℝ)
    (z : SignSequence.{u}) (hz : IsFinite z) (hf : AnalyticAt ℝ f (standardPart z)) :
    analyticTaylorFunction f (standardPart z) z = analyticLift f z hz hf :=
  analyticTaylorFunction_of_isInfinitesimal f _ hf z (infinitesimal_sub_standardPart hz)

/-- At every point of a monad the derivative is the lift of the ordinary derivative. -/
theorem fineHasDerivAt_analyticTaylorFunction_of_isInfinitesimal
    (f : ℝ → ℝ) (c : ℝ) (z : SignSequence.{u})
    (hz : IsInfinitesimal (z - ofReal c)) :
    FineHasDerivAt (analyticTaylorFunction f c) (analyticTaylorFunction (deriv f) c z) z := by
  have hd : analyticTaylorFunction (deriv f) c z =
      powerSeriesEvaluation (z - ofReal c) hz
        (PowerSeries.derivative ℝ (Analytic.taylorSeries f c)) := by
    simp only [analyticTaylorFunction, powerSeriesFunction_of_isInfinitesimal _ _ hz,
      Analytic.taylorSeries_deriv]
  rw [hd]
  unfold analyticTaylorFunction
  have hi : FineHasDerivAt (fun w : SignSequence.{u} => w - ofReal c) 1 z := by
    simpa only [sub_zero] using
      (FineHasDerivAt.id z).sub (FineHasDerivAt.const (ofReal c) z)
  simpa only [mul_one, Function.comp_def] using
    (fineHasDerivAt_powerSeriesFunction (Analytic.taylorSeries f c) (z - ofReal c) hz).comp
      (f := fun w : SignSequence.{u} => w - ofReal c) hi

/-- The Taylor lift is continuous at every point of its infinitesimal monad. -/
theorem continuousAt_analyticTaylorFunction_of_isInfinitesimal
    (f : ℝ → ℝ) (c : ℝ) (z : SignSequence.{u})
    (hz : IsInfinitesimal (z - ofReal c)) :
    ContinuousAt (analyticTaylorFunction f c) z :=
  (fineHasDerivAt_analyticTaylorFunction_of_isInfinitesimal f c z hz).continuousAt

/-- At any finite point, the recentered derivative is the analytic lift of `deriv f`. -/
theorem fineHasDerivAt_analyticTaylorFunction_standardPart
    (f : ℝ → ℝ) (z : SignSequence.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℝ f (standardPart z)) :
    FineHasDerivAt (analyticTaylorFunction f (standardPart z))
      (analyticLift (deriv f) z hz hf.deriv) z := by
  rw [← analyticTaylorFunction_standardPart_eq_analyticLift]
  exact fineHasDerivAt_analyticTaylorFunction_of_isInfinitesimal f _ z
    (infinitesimal_sub_standardPart hz)

end

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

noncomputable section

/-- At every point of a monad the derivative is the lift of the ordinary derivative. -/
theorem fineHasDerivAt_analyticTaylorFunction_of_isInfinitesimal
    (f : ℂ → ℂ) (c : ℂ) (z : Surcomplex.{u})
    (hz : IsInfinitesimal (z - ofComplex c)) :
    FineHasDerivAt (analyticTaylorFunction f c) (analyticTaylorFunction (deriv f) c z) z := by
  have hd : analyticTaylorFunction (deriv f) c z =
      powerSeriesEvaluation (z - ofComplex c) hz
        (PowerSeries.derivative ℂ (Analytic.taylorSeries f c)) := by
    simp only [analyticTaylorFunction, powerSeriesFunction_of_isInfinitesimal _ _ hz,
      Analytic.taylorSeries_deriv]
  rw [hd]
  unfold analyticTaylorFunction
  have hi : FineHasDerivAt (fun w : Surcomplex.{u} => w - ofComplex c) 1 z := by
    simpa only [sub_zero] using
      (FineHasDerivAt.id z).sub (FineHasDerivAt.const (ofComplex c) z)
  simpa only [mul_one, Function.comp_def] using
    (fineHasDerivAt_powerSeriesFunction (Analytic.taylorSeries f c) (z - ofComplex c) hz).comp
      (f := fun w : Surcomplex.{u} => w - ofComplex c) hi

/-- The Taylor lift is continuous at every point of its infinitesimal monad. -/
theorem continuousAt_analyticTaylorFunction_of_isInfinitesimal
    (f : ℂ → ℂ) (c : ℂ) (z : Surcomplex.{u})
    (hz : IsInfinitesimal (z - ofComplex c)) :
    ContinuousAt (analyticTaylorFunction f c) z :=
  (fineHasDerivAt_analyticTaylorFunction_of_isInfinitesimal f c z hz).continuousAt

/-- At any finite point, the recentered derivative is the analytic lift of `deriv f`. -/
theorem fineHasDerivAt_analyticTaylorFunction_standardPart
    (f : ℂ → ℂ) (z : Surcomplex.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℂ f (standardPart z)) :
    FineHasDerivAt (analyticTaylorFunction f (standardPart z))
      (analyticLift (deriv f) z hz hf.deriv) z := by
  rw [← analyticTaylorFunction_standardPart_eq_analyticLift]
  exact fineHasDerivAt_analyticTaylorFunction_of_isInfinitesimal f _ z
    (infinitesimal_sub_standardPart hz)

end

end Surreal.Surcomplex

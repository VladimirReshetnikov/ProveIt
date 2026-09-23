import Surreal.Algebra.AnalyticComposition
import Surreal.Foundations.SignSequenceAnalyticTaylor
import Surreal.Surcomplex.AnalyticTaylor

/-!
# Composition of actual analytic Taylor lifts

This proves the composition clause of `trigonometry:prop:lift` for ordinary
real and complex analytic germs. The inner lift is finite with its prescribed
ordinary value as standard part, so the outer lift is recentered there.
The subtracted inner displacement is infinitesimal, and the existing actual
formal substitution theorem applies without a coefficient-growth bound.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Subtracting the ordinary value from an analytic lift leaves an infinitesimal. -/
theorem infinitesimal_analyticTaylorEvaluation_sub (g : ℝ → ℝ) (c : ℝ)
    (hg : AnalyticAt ℝ g c) (η : SignSequence.{u}) (hη : IsInfinitesimal η) :
    IsInfinitesimal (analyticTaylorEvaluation g c hg η hη - ofReal (g c)) :=
  (infinitesimal_sub_ofReal_iff (isFinite_analyticTaylorEvaluation g c hg η hη)).mpr
    (standardPart_analyticTaylorEvaluation g c hg η hη)

/-- Evaluate an ordinary analytic composite by the two correctly centered Taylor lifts. -/
theorem analyticTaylorEvaluation_comp (f g : ℝ → ℝ) (c : ℝ)
    (hf : AnalyticAt ℝ f (g c)) (hg : AnalyticAt ℝ g c)
    (η : SignSequence.{u}) (hη : IsInfinitesimal η) :
    analyticTaylorEvaluation (f ∘ g) c (hf.comp hg) η hη =
      analyticTaylorEvaluation f (g c) hf
        (analyticTaylorEvaluation g c hg η hη - ofReal (g c))
        (infinitesimal_analyticTaylorEvaluation_sub g c hg η hη) := by
  simp only [analyticTaylorEvaluation]
  rw [Analytic.taylorSeries_comp hf hg, powerSeriesEvaluation_subst _ _ _ _
    (Analytic.constantCoeff_centeredTaylorSeries g c)]
  simp only [Analytic.centeredTaylorSeries, map_sub, powerSeriesEvaluation_C]

/-- Recentered analytic lifting preserves composition on its explicit finite analytic domain. -/
theorem analyticLift_comp (f g : ℝ → ℝ) (z : SignSequence.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℝ f (g (standardPart z))) (hg : AnalyticAt ℝ g (standardPart z)) :
    analyticLift (f ∘ g) z hz (hf.comp hg) =
      analyticLift f (analyticLift g z hz hg) (isFinite_analyticLift g z hz hg)
        (by simpa only [standardPart_analyticLift] using hf) := by
  simpa only [analyticLift, standardPart_analyticTaylorEvaluation] using
    analyticTaylorEvaluation_comp f g (standardPart z) hf hg
      (z - ofReal (standardPart z)) (infinitesimal_sub_standardPart hz)

end

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

noncomputable section

/-- Subtracting the ordinary value from an analytic lift leaves an infinitesimal. -/
theorem infinitesimal_analyticTaylorEvaluation_sub (g : ℂ → ℂ) (c : ℂ)
    (hg : AnalyticAt ℂ g c) (η : Surcomplex.{u}) (hη : IsInfinitesimal η) :
    IsInfinitesimal (analyticTaylorEvaluation g c hg η hη - ofComplex (g c)) :=
  (infinitesimal_sub_ofComplex_iff (isFinite_analyticTaylorEvaluation g c hg η hη)).mpr
    (standardPart_analyticTaylorEvaluation g c hg η hη)

/-- Evaluate an ordinary analytic composite by the two correctly centered Taylor lifts. -/
theorem analyticTaylorEvaluation_comp (f g : ℂ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℂ f (g c)) (hg : AnalyticAt ℂ g c)
    (η : Surcomplex.{u}) (hη : IsInfinitesimal η) :
    analyticTaylorEvaluation (f ∘ g) c (hf.comp hg) η hη =
      analyticTaylorEvaluation f (g c) hf
        (analyticTaylorEvaluation g c hg η hη - ofComplex (g c))
        (infinitesimal_analyticTaylorEvaluation_sub g c hg η hη) := by
  simp only [analyticTaylorEvaluation]
  rw [Analytic.taylorSeries_comp hf hg, powerSeriesEvaluation_subst _ _ _ _
    (Analytic.constantCoeff_centeredTaylorSeries g c)]
  simp only [Analytic.centeredTaylorSeries, map_sub, powerSeriesEvaluation_C]

/-- Recentered analytic lifting preserves composition on its explicit finite analytic domain. -/
theorem analyticLift_comp (f g : ℂ → ℂ) (z : Surcomplex.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℂ f (g (standardPart z))) (hg : AnalyticAt ℂ g (standardPart z)) :
    analyticLift (f ∘ g) z hz (hf.comp hg) =
      analyticLift f (analyticLift g z hz hg) (isFinite_analyticLift g z hz hg)
        (by simpa only [standardPart_analyticLift] using hf) := by
  simpa only [analyticLift, standardPart_analyticTaylorEvaluation] using
    analyticTaylorEvaluation_comp f g (standardPart z) hf hg
      (z - ofComplex (standardPart z)) (infinitesimal_sub_standardPart hz)

end

end Surreal.Surcomplex

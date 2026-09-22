import Surreal.Algebra.AnalyticTaylor
import Surreal.Surcomplex.PowerSeries

/-!
# Recentered Taylor lifting of ordinary holomorphic germs

An explicit ordinary analytic germ at `c` is evaluated only at an actual
infinitesimal displacement from `c`. At a finite input, the center is its
standard part. The ordinary iterated derivatives give the literal strong sum.
This establishes the Taylor rule and its sum/product laws in
`trigonometry:eq:lift` and `trigonometry:prop:lift`, with the recentering required
by `found:rem:recentering`. Fine differentiation and sign lifting are separate.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Evaluate an ordinary analytic germ at an actual infinitesimal displacement.
The analyticity witness makes the ordinary domain of the construction explicit. -/
def analyticTaylorEvaluation (f : ℂ → ℂ) (c : ℂ) (_hf : AnalyticAt ℂ f c)
    (ε : Surcomplex.{u}) (hε : IsInfinitesimal ε) : Surcomplex.{u} :=
  powerSeriesEvaluation ε hε (Analytic.taylorSeries f c)

/-- The displayed ordinary Taylor terms are strongly summable. -/
theorem stronglySummable_analyticTaylor (f : ℂ → ℂ) (c : ℂ)
    (ε : Surcomplex.{u}) (hε : IsInfinitesimal ε) :
    StronglySummable (fun n => ofComplex (iteratedDeriv n f c / n.factorial) * ε ^ n) :=
  stronglySummable_coeff_mul_powers ε hε _

/-- Taylor lifting is literally the strong sum of ordinary derivatives at the center. -/
theorem analyticTaylorEvaluation_eq_strongSum (f : ℂ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℂ f c) (ε : Surcomplex.{u}) (hε : IsInfinitesimal ε) :
    analyticTaylorEvaluation f c hf ε hε =
      strongSum (fun n => ofComplex (iteratedDeriv n f c / n.factorial) * ε ^ n)
        (stronglySummable_analyticTaylor f c ε hε) := by
  simpa only [analyticTaylorEvaluation, Analytic.coeff_taylorSeries] using
    powerSeriesEvaluation_eq_strongSum ε hε (Analytic.taylorSeries f c)

theorem isFinite_analyticTaylorEvaluation (f : ℂ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℂ f c) (ε : Surcomplex.{u}) (hε : IsInfinitesimal ε) :
    IsFinite (analyticTaylorEvaluation f c hf ε hε) :=
  isFinite_powerSeriesEvaluation ε hε _

@[simp] theorem standardPart_analyticTaylorEvaluation (f : ℂ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℂ f c) (ε : Surcomplex.{u}) (hε : IsInfinitesimal ε) :
    standardPart (analyticTaylorEvaluation f c hf ε hε) = f c := by
  simp [analyticTaylorEvaluation]

/-- Substitution at zero returns the ordinary value, before any infinitesimal correction. -/
@[simp] theorem analyticTaylorEvaluation_zero (f : ℂ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℂ f c) :
    analyticTaylorEvaluation f c hf (0 : Surcomplex.{u})
      ⟨SignSequence.infinitesimal_zero, SignSequence.infinitesimal_zero⟩ = ofComplex (f c) := by
  simp [analyticTaylorEvaluation]

theorem analyticTaylorEvaluation_congr {f g : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hg : AnalyticAt ℂ g c) (h : f =ᶠ[nhds c] g)
    (ε : Surcomplex.{u}) (hε : IsInfinitesimal ε) :
    analyticTaylorEvaluation f c hf ε hε = analyticTaylorEvaluation g c hg ε hε := by
  simp only [analyticTaylorEvaluation, Analytic.taylorSeries_congr h]

theorem analyticTaylorEvaluation_add {f g : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hg : AnalyticAt ℂ g c)
    (ε : Surcomplex.{u}) (hε : IsInfinitesimal ε) :
    analyticTaylorEvaluation (f + g) c (hf.add hg) ε hε =
      analyticTaylorEvaluation f c hf ε hε + analyticTaylorEvaluation g c hg ε hε := by
  simp only [analyticTaylorEvaluation, Analytic.taylorSeries_add hf hg, map_add]

theorem analyticTaylorEvaluation_mul {f g : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hg : AnalyticAt ℂ g c)
    (ε : Surcomplex.{u}) (hε : IsInfinitesimal ε) :
    analyticTaylorEvaluation (f * g) c (hf.mul hg) ε hε =
      analyticTaylorEvaluation f c hf ε hε * analyticTaylorEvaluation g c hg ε hε := by
  simp only [analyticTaylorEvaluation, Analytic.taylorSeries_mul hf hg, map_mul]

@[simp] theorem analyticTaylorEvaluation_const (r c : ℂ)
    (ε : Surcomplex.{u}) (hε : IsInfinitesimal ε) :
    analyticTaylorEvaluation (fun _ => r) c (analyticAt_const) ε hε = ofComplex r := by
  simp [analyticTaylorEvaluation]

/-- The recentered lift on its explicit domain of finite inputs with analytic standard part. -/
def analyticLift (f : ℂ → ℂ) (z : Surcomplex.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℂ f (standardPart z)) : Surcomplex.{u} :=
  analyticTaylorEvaluation f (standardPart z) hf
    (z - ofComplex (standardPart z)) (infinitesimal_sub_standardPart hz)

theorem isFinite_analyticLift (f : ℂ → ℂ) (z : Surcomplex.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℂ f (standardPart z)) : IsFinite (analyticLift f z hz hf) :=
  isFinite_analyticTaylorEvaluation _ _ _ _ _

@[simp] theorem standardPart_analyticLift (f : ℂ → ℂ) (z : Surcomplex.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℂ f (standardPart z)) :
    standardPart (analyticLift f z hz hf) = f (standardPart z) :=
  standardPart_analyticTaylorEvaluation _ _ _ _ _

theorem analyticLift_eq_strongSum (f : ℂ → ℂ) (z : Surcomplex.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℂ f (standardPart z)) :
    analyticLift f z hz hf =
      strongSum (fun n => ofComplex (iteratedDeriv n f (standardPart z) / n.factorial) *
        (z - ofComplex (standardPart z)) ^ n)
        (stronglySummable_analyticTaylor f _ _ (infinitesimal_sub_standardPart hz)) :=
  analyticTaylorEvaluation_eq_strongSum _ _ _ _ _

@[simp] theorem analyticLift_ofComplex (f : ℂ → ℂ) (c : ℂ) (hf : AnalyticAt ℂ f c) :
    analyticLift f (ofComplex c : Surcomplex.{u}) (finite_ofComplex c)
      (by simpa using hf) = ofComplex (f c) := by
  simp [analyticLift, analyticTaylorEvaluation]

theorem analyticLift_add {f g : ℂ → ℂ} (z : Surcomplex.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℂ f (standardPart z)) (hg : AnalyticAt ℂ g (standardPart z)) :
    analyticLift (f + g) z hz (hf.add hg) = analyticLift f z hz hf + analyticLift g z hz hg :=
  analyticTaylorEvaluation_add hf hg _ _

theorem analyticLift_mul {f g : ℂ → ℂ} (z : Surcomplex.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℂ f (standardPart z)) (hg : AnalyticAt ℂ g (standardPart z)) :
    analyticLift (f * g) z hz (hf.mul hg) = analyticLift f z hz hf * analyticLift g z hz hg :=
  analyticTaylorEvaluation_mul hf hg _ _

end

end Surreal.Surcomplex

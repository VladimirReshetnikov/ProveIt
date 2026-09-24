import Surreal.Foundations.SignSequenceAnalyticTaylor
import Surreal.Surcomplex.AnalyticTaylor
import Surreal.Surcomplex.PowerSeriesLeadingFactor

/-!
# Leading-term test for lifted ordinary analytic germs

This proves all three claims in `trigonometry:lem:leading`: an exact leading
monomial times one plus an infinitesimal, the valuation formula, and agreement
of leading coefficients. The ordinary zero order is expressed by vanishing
of every lower iterated derivative and nonvanishing of the derivative at `m`.
Both actual fields are covered, with no coefficient-growth restriction.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The leading monomial of the ordinary germ has an infinitesimal relative error. -/
theorem exists_infinitesimal_analyticTaylor_factor (f : ℝ → ℝ) (c : ℝ)
    (hf : AnalyticAt ℝ f c) (m : ℕ) (hm : iteratedDeriv m f c ≠ 0)
    (hvan : ∀ n < m, iteratedDeriv n f c = 0)
    (η : SignSequence.{u}) (hη : IsInfinitesimal η) :
    ∃ ξ : SignSequence.{u}, IsInfinitesimal ξ ∧
      analyticTaylorEvaluation f c hf η hη =
        ofReal (iteratedDeriv m f c / m.factorial) * η ^ m * (1 + ξ) := by
  have ho := Analytic.order_taylorSeries_eq f c m hm hvan
  have hn := Analytic.taylorSeries_ne_zero_of_iteratedDeriv_ne_zero f c m hm
  simpa only [analyticTaylorEvaluation, ho, ENat.toNat_coe, Analytic.coeff_taylorSeries] using
    exists_infinitesimal_powerSeries_factor η hη (Analytic.taylorSeries f c) hn

/-- A lifted germ of ordinary order `m` has valuation `m` times the input valuation. -/
theorem valuation_analyticTaylorEvaluation (f : ℝ → ℝ) (c : ℝ)
    (hf : AnalyticAt ℝ f c) (m : ℕ) (hm : iteratedDeriv m f c ≠ 0)
    (hvan : ∀ n < m, iteratedDeriv n f c = 0)
    (η : SignSequence.{u}) (hη : IsInfinitesimal η) :
    valuation (analyticTaylorEvaluation f c hf η hη) = m • valuation η := by
  have ho := Analytic.order_taylorSeries_eq f c m hm hvan
  have hn := Analytic.taylorSeries_ne_zero_of_iteratedDeriv_ne_zero f c m hm
  simpa only [analyticTaylorEvaluation, ho, ENat.toNat_coe] using
    valuation_powerSeriesEvaluation η hη (Analytic.taylorSeries f c) hn

/-- The lifted germ and its leading monomial have exactly the same leading coefficient. -/
theorem leadingCoeff_analyticTaylorEvaluation (f : ℝ → ℝ) (c : ℝ)
    (hf : AnalyticAt ℝ f c) (m : ℕ) (hm : iteratedDeriv m f c ≠ 0)
    (hvan : ∀ n < m, iteratedDeriv n f c = 0)
    (η : SignSequence.{u}) (hη : IsInfinitesimal η) :
    leadingCoeff (analyticTaylorEvaluation f c hf η hη) =
      leadingCoeff (ofReal (iteratedDeriv m f c / m.factorial) * η ^ m) := by
  have ho := Analytic.order_taylorSeries_eq f c m hm hvan
  have hn := Analytic.taylorSeries_ne_zero_of_iteratedDeriv_ne_zero f c m hm
  simpa only [analyticTaylorEvaluation, ho, ENat.toNat_coe, Analytic.coeff_taylorSeries,
    leadingCoeff_mul, leadingCoeff_ofReal, leadingCoeff_pow] using
    leadingCoeff_powerSeriesEvaluation η hη (Analytic.taylorSeries f c) hn

/-- A finite-order analytic germ does not vanish at a nonzero actual infinitesimal displacement. -/
theorem analyticTaylorEvaluation_ne_zero (f : ℝ → ℝ) (c : ℝ)
    (hf : AnalyticAt ℝ f c) (m : ℕ) (hm : iteratedDeriv m f c ≠ 0)
    (η : SignSequence.{u}) (hη : IsInfinitesimal η) (hne : η ≠ 0) :
    analyticTaylorEvaluation f c hf η hη ≠ 0 := by
  intro h
  have he : powerSeriesEvaluation η hη (Analytic.taylorSeries f c) =
      powerSeriesEvaluation η hη 0 := by
    simpa only [map_zero, analyticTaylorEvaluation] using h
  exact Analytic.taylorSeries_ne_zero_of_iteratedDeriv_ne_zero f c m hm
    (powerSeriesEvaluation_injective η hη hne he)

/-- For a real germ, its first nonzero Taylor monomial decides its strict sign. -/
theorem analyticTaylorEvaluation_pos_iff_leading (f : ℝ → ℝ) (c : ℝ)
    (hf : AnalyticAt ℝ f c) (m : ℕ) (hm : iteratedDeriv m f c ≠ 0)
    (hvan : ∀ n < m, iteratedDeriv n f c = 0)
    (η : SignSequence.{u}) (hη : IsInfinitesimal η) :
    0 < analyticTaylorEvaluation f c hf η hη ↔
      0 < ofReal (iteratedDeriv m f c / m.factorial) * η ^ m := by
  rw [← leadingCoeff_pos_iff, leadingCoeff_analyticTaylorEvaluation f c hf m hm hvan,
    leadingCoeff_pos_iff]

/-- The first nonzero Taylor monomial also decides negativity. -/
theorem analyticTaylorEvaluation_neg_iff_leading (f : ℝ → ℝ) (c : ℝ)
    (hf : AnalyticAt ℝ f c) (m : ℕ) (hm : iteratedDeriv m f c ≠ 0)
    (hvan : ∀ n < m, iteratedDeriv n f c = 0)
    (η : SignSequence.{u}) (hη : IsInfinitesimal η) :
    analyticTaylorEvaluation f c hf η hη < 0 ↔
      ofReal (iteratedDeriv m f c / m.factorial) * η ^ m < 0 := by
  have hneg (x : SignSequence.{u}) : leadingCoeff x < 0 ↔ x < 0 := by
    simpa only [leadingCoeff_neg, neg_pos] using leadingCoeff_pos_iff (-x)
  rw [← hneg, leadingCoeff_analyticTaylorEvaluation f c hf m hm hvan, hneg]

/-- The leading-term sign criterion includes equality and endpoint zero cases. -/
theorem analyticTaylorEvaluation_nonneg_iff_leading (f : ℝ → ℝ) (c : ℝ)
    (hf : AnalyticAt ℝ f c) (m : ℕ) (hm : iteratedDeriv m f c ≠ 0)
    (hvan : ∀ n < m, iteratedDeriv n f c = 0)
    (η : SignSequence.{u}) (hη : IsInfinitesimal η) :
    0 ≤ analyticTaylorEvaluation f c hf η hη ↔
      0 ≤ ofReal (iteratedDeriv m f c / m.factorial) * η ^ m := by
  simpa only [not_lt] using not_congr
    (analyticTaylorEvaluation_neg_iff_leading f c hf m hm hvan η hη)

/-- A strict ordinary positive margin stays positive throughout the monad. -/
theorem analyticTaylorEvaluation_pos_of_pos (f : ℝ → ℝ) (c : ℝ)
    (hf : AnalyticAt ℝ f c) (hpos : 0 < f c)
    (η : SignSequence.{u}) (hη : IsInfinitesimal η) :
    0 < analyticTaylorEvaluation f c hf η hη := by
  have hm : iteratedDeriv 0 f c ≠ 0 := hpos.ne'
  rw [analyticTaylorEvaluation_pos_iff_leading f c hf 0 hm (by omega)]
  simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    pow_zero, mul_one, map_zero] using ofReal_strictMono hpos

/-- A positive first coefficient of even order stays nonnegative on both sides. -/
theorem analyticTaylorEvaluation_nonneg_of_even (f : ℝ → ℝ) (c : ℝ)
    (hf : AnalyticAt ℝ f c) (m : ℕ) (heven : Even m)
    (hpos : 0 < iteratedDeriv m f c) (hvan : ∀ n < m, iteratedDeriv n f c = 0)
    (η : SignSequence.{u}) (hη : IsInfinitesimal η) :
    0 ≤ analyticTaylorEvaluation f c hf η hη := by
  rw [analyticTaylorEvaluation_nonneg_iff_leading f c hf m hpos.ne' hvan]
  apply mul_nonneg
  · have hp : (0 : SignSequence.{u}) < ofReal (iteratedDeriv m f c / m.factorial) := by
      simpa only [map_zero] using
        ofReal_strictMono (div_pos hpos (show (0 : ℝ) < m.factorial by positivity))
    exact hp.le
  · exact heven.pow_nonneg η

end

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

noncomputable section

/-- The leading monomial of the ordinary germ has an infinitesimal relative error. -/
theorem exists_infinitesimal_analyticTaylor_factor (f : ℂ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℂ f c) (m : ℕ) (hm : iteratedDeriv m f c ≠ 0)
    (hvan : ∀ n < m, iteratedDeriv n f c = 0)
    (η : Surcomplex.{u}) (hη : IsInfinitesimal η) :
    ∃ ξ : Surcomplex.{u}, IsInfinitesimal ξ ∧
      analyticTaylorEvaluation f c hf η hη =
        ofComplex (iteratedDeriv m f c / m.factorial) * η ^ m * (1 + ξ) := by
  have ho := Analytic.order_taylorSeries_eq f c m hm hvan
  have hn := Analytic.taylorSeries_ne_zero_of_iteratedDeriv_ne_zero f c m hm
  simpa only [analyticTaylorEvaluation, ho, ENat.toNat_coe, Analytic.coeff_taylorSeries] using
    exists_infinitesimal_powerSeries_factor η hη (Analytic.taylorSeries f c) hn

/-- A lifted germ of ordinary order `m` has valuation `m` times the input valuation. -/
theorem valuation_analyticTaylorEvaluation (f : ℂ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℂ f c) (m : ℕ) (hm : iteratedDeriv m f c ≠ 0)
    (hvan : ∀ n < m, iteratedDeriv n f c = 0)
    (η : Surcomplex.{u}) (hη : IsInfinitesimal η) :
    valuation (analyticTaylorEvaluation f c hf η hη) = m • valuation η := by
  have ho := Analytic.order_taylorSeries_eq f c m hm hvan
  have hn := Analytic.taylorSeries_ne_zero_of_iteratedDeriv_ne_zero f c m hm
  simpa only [analyticTaylorEvaluation, ho, ENat.toNat_coe] using
    valuation_powerSeriesEvaluation η hη (Analytic.taylorSeries f c) hn

/-- The lifted germ and its leading monomial have exactly the same leading coefficient. -/
theorem leadingCoeff_analyticTaylorEvaluation (f : ℂ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℂ f c) (m : ℕ) (hm : iteratedDeriv m f c ≠ 0)
    (hvan : ∀ n < m, iteratedDeriv n f c = 0)
    (η : Surcomplex.{u}) (hη : IsInfinitesimal η) :
    leadingCoeff (analyticTaylorEvaluation f c hf η hη) =
      leadingCoeff (ofComplex (iteratedDeriv m f c / m.factorial) * η ^ m) := by
  have ho := Analytic.order_taylorSeries_eq f c m hm hvan
  have hn := Analytic.taylorSeries_ne_zero_of_iteratedDeriv_ne_zero f c m hm
  simpa only [analyticTaylorEvaluation, ho, ENat.toNat_coe, Analytic.coeff_taylorSeries,
    leadingCoeff_mul, leadingCoeff_ofComplex, leadingCoeff_pow] using
    leadingCoeff_powerSeriesEvaluation η hη (Analytic.taylorSeries f c) hn

/-- A finite-order analytic germ does not vanish at a nonzero actual infinitesimal displacement. -/
theorem analyticTaylorEvaluation_ne_zero (f : ℂ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℂ f c) (m : ℕ) (hm : iteratedDeriv m f c ≠ 0)
    (η : Surcomplex.{u}) (hη : IsInfinitesimal η) (hne : η ≠ 0) :
    analyticTaylorEvaluation f c hf η hη ≠ 0 := by
  intro h
  have he : powerSeriesEvaluation η hη (Analytic.taylorSeries f c) =
      powerSeriesEvaluation η hη 0 := by
    simpa only [map_zero, analyticTaylorEvaluation] using h
  exact Analytic.taylorSeries_ne_zero_of_iteratedDeriv_ne_zero f c m hm
    (powerSeriesEvaluation_injective η hη hne he)

end

end Surreal.Surcomplex

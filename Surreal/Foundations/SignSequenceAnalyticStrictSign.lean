import Surreal.Surcomplex.AnalyticLiftCalculus

/-!
# Strict positivity of analytic lifts on open ordinary intervals

This is the strict form of the sign argument used in `trigonometry:prop:order`.
The nonnegative closed-interval lift, injective nonzero-infinitesimal evaluation,
and ordinary analyticity together handle displacements from either endpoint.
No global monotonicity is inferred from a fine derivative.
-/

universe u

namespace Surreal.Foundations.SignSequence

/-- Ordinary analytic positivity throughout an open interval lifts to every actual interior point. -/
theorem analyticLiftFunction_pos_of_mem_Ioo (f : ℝ → ℝ) (a b : ℝ)
    (hf : AnalyticOnNhd ℝ f (Set.Icc a b)) (hpos : ∀ y ∈ Set.Ioo a b, 0 < f y)
    (x : SignSequence.{u}) (hx : x ∈ Set.Ioo (ofReal a) (ofReal b)) :
    0 < analyticLiftFunction f x := by
  have hab : a < b := ofReal_strictMono.lt_iff_lt.mp (hx.1.trans hx.2)
  have hxc : x ∈ Set.Icc (ofReal a) (ofReal b) := ⟨hx.1.le, hx.2.le⟩
  have hfinite := isFinite_of_mem_real_Icc hxc
  have hc := standardPart_mem_real_Icc hxc
  have hn := analyticLiftFunction_nonneg_of_mem_Icc f a b hf
    (Analytic.nonneg_on_Icc_of_pos_on_Ioo hab hf hpos) x hxc
  by_cases hzero : x - ofReal (standardPart x) = 0
  · have he : x = ofReal (standardPart x) := sub_eq_zero.mp hzero
    have hc' : standardPart x ∈ Set.Ioo a b := by
      constructor
      · exact ofReal_strictMono.lt_iff_lt.mp (he ▸ hx.1)
      · exact ofReal_strictMono.lt_iff_lt.mp (he ▸ hx.2)
    rw [he, analyticLiftFunction_ofReal f _ (hf _ hc)]
    simpa only [map_zero] using ofReal_strictMono (hpos _ hc')
  · apply lt_of_le_of_ne hn
    intro he
    have he' : powerSeriesEvaluation (x - ofReal (standardPart x))
        (infinitesimal_sub_standardPart hfinite) (Analytic.taylorSeries f (standardPart x)) =
        powerSeriesEvaluation (x - ofReal (standardPart x))
          (infinitesimal_sub_standardPart hfinite) 0 := by
      rw [analyticLiftFunction_of_domain f x hfinite (hf _ hc)] at he
      simpa only [analyticLift, analyticTaylorEvaluation, map_zero] using he.symm
    exact Analytic.taylorSeries_ne_zero_of_pos_on_Ioo hab (hf _ hc) hc hpos
      (powerSeriesEvaluation_injective _ _ hzero he')

/-- Global ordinary analytic nonnegativity lifts at every finite actual input. -/
theorem analyticLiftFunction_nonneg (f : ℝ → ℝ) (hf : ∀ r, AnalyticAt ℝ f r)
    (hpos : ∀ r, 0 ≤ f r) (x : SignSequence.{u}) (hx : IsFinite x) :
    0 ≤ analyticLiftFunction f x := by
  obtain ⟨n, hn⟩ := (isFinite_iff_exists_nat_abs_le x).mp hx
  apply analyticLiftFunction_nonneg_of_mem_Icc f (-(n : ℝ)) n
    (fun r _ => hf r) (fun r _ => hpos r) x
  simpa only [map_neg, map_natCast, Set.mem_Icc] using abs_le.mp hn

end Surreal.Foundations.SignSequence

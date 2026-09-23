import Surreal.Algebra.AnalyticSign
import Surreal.Surcomplex.AnalyticLeading

/-!
# Nonnegativity of analytic lifts on closed ordinary intervals

This proves the sign-lifting clause of `trigonometry:prop:lift` on the actual
surreal field, including both endpoints and degenerate intervals. Ordinary
one-sided signs constrain the first Taylor coefficient, and the proved actual
leading-term test transports the sign. A zero Taylor series is treated directly.
-/

universe u

namespace Surreal.Foundations.SignSequence

open Filter Topology

noncomputable section

/-- An ordinary bounded interval contains only finite surreals. -/
theorem isFinite_of_mem_real_Icc {a b : ℝ} {x : SignSequence.{u}}
    (hx : x ∈ Set.Icc (ofReal a) (ofReal b)) : IsFinite x := by
  obtain ⟨na, hna⟩ := (isFinite_iff_exists_nat_abs_le _).mp (finite_ofReal a)
  obtain ⟨nb, hnb⟩ := (isFinite_iff_exists_nat_abs_le _).mp (finite_ofReal b)
  apply (isFinite_iff_exists_nat_abs_le x).mpr
  refine ⟨na + nb, abs_le.mpr ⟨?_, ?_⟩⟩
  · have h := (abs_le.mp hna).1.trans hx.1
    push_cast
    have : (0 : SignSequence.{u}) ≤ nb := Nat.cast_nonneg nb
    linarith
  · have h := hx.2.trans (abs_le.mp hnb).2
    push_cast
    have : (0 : SignSequence.{u}) ≤ na := Nat.cast_nonneg na
    linarith

/-- The standard part remains inside the same closed ordinary interval. -/
theorem standardPart_mem_real_Icc {a b : ℝ} {x : SignSequence.{u}}
    (hx : x ∈ Set.Icc (ofReal a) (ofReal b)) : standardPart x ∈ Set.Icc a b := by
  have hfinite := isFinite_of_mem_real_Icc hx
  exact ⟨ArchimedeanClass.le_stdPart_of_le ofReal hfinite hx.1,
    ArchimedeanClass.stdPart_le_of_le ofReal hfinite hx.2⟩

/-- Nonnegativity transfers to every allowed infinitesimal displacement in a closed interval. -/
theorem analyticTaylorEvaluation_nonneg_of_mem_Icc (f : ℝ → ℝ) (a b c : ℝ)
    (hf : AnalyticAt ℝ f c) (hc : c ∈ Set.Icc a b)
    (hpos : ∀ y ∈ Set.Icc a b, 0 ≤ f y)
    (η : SignSequence.{u}) (hη : IsInfinitesimal η)
    (hx : ofReal c + η ∈ Set.Icc (ofReal a) (ofReal b)) :
    0 ≤ analyticTaylorEvaluation f c hf η hη := by
  by_cases hzero : η = 0
  · subst η
    rw [analyticTaylorEvaluation_zero]
    simpa only [map_zero] using ofReal_strictMono.monotone (hpos c hc)
  by_cases hF : Analytic.taylorSeries f c = 0
  · simp only [analyticTaylorEvaluation, hF, map_zero, le_refl]
  let m := (Analytic.taylorSeries f c).order.toNat
  have hm : iteratedDeriv m f c ≠ 0 := by
    have h := PowerSeries.coeff_order hF
    rw [Analytic.coeff_taylorSeries] at h
    exact (div_ne_zero_iff.mp h).1
  have hvan : ∀ n < m, iteratedDeriv n f c = 0 := by
    intro n hn
    have h := PowerSeries.coeff_of_lt_order_toNat (φ := Analytic.taylorSeries f c) n hn
    rw [Analytic.coeff_taylorSeries, div_eq_zero_iff] at h
    exact h.resolve_right (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  rw [analyticTaylorEvaluation_nonneg_iff_leading f c hf m hm hvan]
  rcases lt_or_gt_of_ne hzero with hneg | hpositive
  · have hac : a < c := by
      by_contra h
      have he : a = c := le_antisymm hc.1 (le_of_not_gt h)
      have hh := hx.1
      rw [he] at hh
      linarith
    have hleft : ∀ᶠ y in 𝓝[<] c, 0 ≤ f y := by
      filter_upwards [(eventually_gt_nhds hac).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with y hay hyc
      exact hpos y ⟨hay.le, (show y < c from hyc).le.trans hc.2⟩
    have hcoef := Analytic.taylorCoeff_nonneg_of_eventually_left hf m hvan hleft
    have he : ofReal (iteratedDeriv m f c / m.factorial) * η ^ m =
        ofReal ((-1 : ℝ) ^ m * (iteratedDeriv m f c / m.factorial)) * (-η) ^ m := by
      calc
        _ = ofReal (iteratedDeriv m f c / m.factorial) * ((-1) * (-η)) ^ m := by
          rw [neg_one_mul, neg_neg]
        _ = _ := by rw [mul_pow, map_mul, map_pow, map_neg, map_one]; ring
    rw [he]
    exact mul_nonneg (by simpa only [map_zero] using ofReal_strictMono.monotone hcoef)
      (pow_nonneg (neg_nonneg.mpr hneg.le) _)
  · have hcb : c < b := by
      by_contra h
      have he : c = b := le_antisymm hc.2 (le_of_not_gt h)
      have hh := hx.2
      rw [← he] at hh
      linarith
    have hright : ∀ᶠ y in 𝓝[>] c, 0 ≤ f y := by
      filter_upwards [(eventually_lt_nhds hcb).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with y hyb hcy
      exact hpos y ⟨hc.1.trans (show c < y from hcy).le, hyb.le⟩
    have hcoef := Analytic.taylorCoeff_nonneg_of_eventually_right hf m hvan hright
    exact mul_nonneg (by simpa only [map_zero] using ofReal_strictMono.monotone hcoef)
      (pow_nonneg hpositive.le _)

/-- The complete closed-interval sign-lifting assertion, with finiteness derived from the interval. -/
theorem analyticLift_nonneg_of_mem_Icc (f : ℝ → ℝ) (a b : ℝ)
    (hf : AnalyticOnNhd ℝ f (Set.Icc a b)) (hpos : ∀ y ∈ Set.Icc a b, 0 ≤ f y)
    (x : SignSequence.{u}) (hx : x ∈ Set.Icc (ofReal a) (ofReal b)) :
    0 ≤ analyticLift f x (isFinite_of_mem_real_Icc hx)
      (hf (standardPart x) (standardPart_mem_real_Icc hx)) := by
  apply analyticTaylorEvaluation_nonneg_of_mem_Icc f a b (standardPart x)
    (hf _ (standardPart_mem_real_Icc hx)) (standardPart_mem_real_Icc hx) hpos
  simpa only [add_sub_cancel] using hx

end

end Surreal.Foundations.SignSequence

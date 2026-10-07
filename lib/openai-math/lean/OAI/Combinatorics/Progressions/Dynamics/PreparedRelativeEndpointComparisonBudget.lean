import OAI.Combinatorics.Progressions.Polynomial.PreparedEndpointPerturbationPolynomial

namespace OAI

section

namespace Erdos3.VectorPolynomial

def preparedRelativeEndpointTestLog (localBudget earlyNative : ℝ) : ℝ :=
  max localBudget (3 * earlyNative + 3)

def preparedRelativeEndpointComparisonLog
    (localBudget earlyNative earlyMass u p cost : ℝ) : ℝ :=
  max (preparedRelativeEndpointTestLog localBudget earlyNative)
    (2 * u + 4 * p + max 0 earlyMass + 20) + 2 + cost + cost + 8

theorem preparedRelativeEndpointTestLog_nonneg {localBudget earlyNative : ℝ}
    (hlocal : 0 ≤ localBudget) :
    0 ≤ preparedRelativeEndpointTestLog localBudget earlyNative :=
  hlocal.trans (le_max_left _ _)

theorem preparedRelativeEndpointTestLog_local (localBudget earlyNative : ℝ) :
    localBudget ≤ preparedRelativeEndpointTestLog localBudget earlyNative :=
  le_max_left _ _

theorem preparedRelativeEndpointTestLog_native (localBudget earlyNative : ℝ) :
    3 * earlyNative + 3 ≤ preparedRelativeEndpointTestLog localBudget earlyNative :=
  le_max_right _ _

theorem preparedRelativeEndpointComparisonLog_nonneg
    {localBudget earlyNative earlyMass u p cost : ℝ}
    (hlocal : 0 ≤ localBudget) (hcost : 0 ≤ cost) :
    0 ≤ preparedRelativeEndpointComparisonLog localBudget earlyNative earlyMass u p cost := by
  have ht := preparedRelativeEndpointTestLog_nonneg (earlyNative := earlyNative) hlocal
  have hm := le_max_left (preparedRelativeEndpointTestLog localBudget earlyNative)
    (2 * u + 4 * p + max 0 earlyMass + 20)
  unfold preparedRelativeEndpointComparisonLog
  linarith only [ht, hm, hcost]

theorem preparedRelativeEndpointComparisonLog_test_precision
    (localBudget earlyNative earlyMass u p cost : ℝ) :
    preparedRelativeEndpointTestLog localBudget earlyNative + 2 + cost + cost + 8 ≤
      preparedRelativeEndpointComparisonLog localBudget earlyNative earlyMass u p cost := by
  unfold preparedRelativeEndpointComparisonLog
  linarith only [le_max_left (preparedRelativeEndpointTestLog localBudget earlyNative)
    (2 * u + 4 * p + max 0 earlyMass + 20)]

theorem preparedRelativeEndpointComparisonLog_model_precision
    {localBudget earlyNative earlyMass native mass u p cost : ℝ}
    (hnative : native ≤ earlyNative) (hmass : mass ≤ earlyMass) :
    max (max localBudget (3 * native + 3)) (2 * u + 4 * p + max 0 mass + 20) +
        2 + cost + cost + 8 ≤
      preparedRelativeEndpointComparisonLog localBudget earlyNative earlyMass u p cost := by
  have htest : max localBudget (3 * native + 3) ≤
      preparedRelativeEndpointTestLog localBudget earlyNative :=
    max_le_max le_rfl (by linarith only [hnative])
  have hmodel : 2 * u + 4 * p + max 0 mass + 20 ≤
      2 * u + 4 * p + max 0 earlyMass + 20 := by
    linarith only [max_le_max (le_refl (0 : ℝ)) hmass]
  have hmax := max_le_max htest hmodel
  unfold preparedRelativeEndpointComparisonLog
  linarith only [hmax]

theorem preparedRelativeEndpointComparisonLog_forecast_accuracy
    {localBudget earlyNative earlyMass u p cost : ℝ} (hcost : 0 ≤ cost) :
    2 * u + 4 * p + 12 ≤
      preparedRelativeEndpointComparisonLog localBudget earlyNative earlyMass u p cost := by
  have hmax := le_max_right (preparedRelativeEndpointTestLog localBudget earlyNative)
    (2 * u + 4 * p + max 0 earlyMass + 20)
  have hmass : 0 ≤ max 0 earlyMass := le_max_left _ _
  unfold preparedRelativeEndpointComparisonLog
  linarith only [hmax, hmass, hcost]

theorem exists_preparedRelativeEndpointComparisonLog_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {t localBudget earlyNative earlyMass u p cost : ℝ},
      0 ≤ t → localBudget ∈ Set.Icc 0 t → earlyNative ∈ Set.Icc 0 t →
      earlyMass ∈ Set.Icc 0 t → u ∈ Set.Icc 0 t → p ∈ Set.Icc 0 t →
      cost ∈ Set.Icc 0 t →
      preparedRelativeEndpointTestLog localBudget earlyNative ∈ Set.Icc 0 ((t + C) ^ C) ∧
      preparedRelativeEndpointComparisonLog localBudget earlyNative earlyMass u p cost ∈
        Set.Icc 0 ((t + C) ^ C) := by
  let poly : Polynomial ℕ := 9 * Polynomial.X + 30
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro t localBudget earlyNative earlyMass u p cost ht hlocal hnative hmass hu hp hcost
  have htest : preparedRelativeEndpointTestLog localBudget earlyNative ≤ 3 * t + 3 :=
    max_le (by linarith only [hlocal.2, ht]) (by linarith only [hnative.2])
  have hmodel : max (preparedRelativeEndpointTestLog localBudget earlyNative)
      (2 * u + 4 * p + max 0 earlyMass + 20) ≤ 7 * t + 20 := by
    rw [max_eq_right hmass.1]
    exact max_le (by linarith only [htest, ht])
      (by linarith only [hu.2, hp.2, hmass.2])
  have hcompare : preparedRelativeEndpointComparisonLog localBudget earlyNative earlyMass u p cost ≤
      9 * t + 30 := by
    unfold preparedRelativeEndpointComparisonLog
    linarith only [hmodel, hcost.2]
  have hbound : 9 * t + 30 ≤ (t + C) ^ C := by
    simpa [poly] using hpoly t ht
  exact ⟨⟨preparedRelativeEndpointTestLog_nonneg hlocal.1,
      (by linarith only [htest, ht] : preparedRelativeEndpointTestLog localBudget earlyNative ≤
        9 * t + 30).trans hbound⟩,
    ⟨preparedRelativeEndpointComparisonLog_nonneg hlocal.1 hcost.1, hcompare.trans hbound⟩⟩

def preparedRelativeEndpointSourceLog (D primitiveCap Ptest : ℝ) : ℝ :=
  2 + D ^ 2 + primitiveCap + max 0 Ptest

def preparedRelativeEndpointCoarseLog (D primitiveCap Ptest Ecompare : ℝ) : ℝ :=
  2 * preparedRelativeEndpointSourceLog D primitiveCap Ptest + Ecompare + 18

noncomputable def preparedRelativeEndpointSigmaLog
    (D primitiveCap Ptest Ecompare cost : ℝ) (m : ℕ) : ℝ :=
  fixedPathSlicedPerturbationLog D
    (D + preparedRelativeEndpointSourceLog D primitiveCap Ptest + 4) (cost + 1)
    (preparedRelativeEndpointCoarseLog D primitiveCap Ptest Ecompare) m

theorem preparedRelativeEndpointSourceLog_nonneg {D primitiveCap Ptest : ℝ}
    (hcap : 0 ≤ primitiveCap) : 0 ≤ preparedRelativeEndpointSourceLog D primitiveCap Ptest := by
  unfold preparedRelativeEndpointSourceLog
  positivity

theorem preparedRelativeEndpointCoarseLog_nonneg {D primitiveCap Ptest Ecompare : ℝ}
    (hcap : 0 ≤ primitiveCap) (hE : 0 ≤ Ecompare) :
    0 ≤ preparedRelativeEndpointCoarseLog D primitiveCap Ptest Ecompare := by
  have hsource := preparedRelativeEndpointSourceLog_nonneg (D := D) (Ptest := Ptest) hcap
  unfold preparedRelativeEndpointCoarseLog
  positivity

theorem preparedRelativeEndpointSigmaLog_nonneg {D primitiveCap Ptest Ecompare cost : ℝ}
    (hD : 0 ≤ D) (hcap : 0 ≤ primitiveCap) (hE : 0 ≤ Ecompare) (hcost : 0 ≤ cost) (m : ℕ) :
    0 ≤ preparedRelativeEndpointSigmaLog D primitiveCap Ptest Ecompare cost m := by
  have hsource := preparedRelativeEndpointSourceLog_nonneg (D := D) (Ptest := Ptest) hcap
  exact fixedPathSlicedPerturbationLog_nonneg hD (by positivity) (by positivity)
    (preparedRelativeEndpointCoarseLog_nonneg hcap hE) m

theorem exists_preparedRelativeEndpointPerturbationLog_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {t D primitiveCap Ptest Ecompare cost : ℝ},
      0 ≤ t → D ∈ Set.Icc 0 t → primitiveCap ∈ Set.Icc 0 t →
      Ptest ∈ Set.Icc 0 t → Ecompare ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t →
      preparedRelativeEndpointSigmaLog D primitiveCap Ptest Ecompare cost m ∈
        Set.Icc 0 ((t + C) ^ C) ∧
      preparedRelativeEndpointCoarseLog D primitiveCap Ptest Ecompare ∈
        Set.Icc 0 ((t + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedEndpointPerturbation_budget m
  refine ⟨C, hC, ?_⟩
  intro t D primitiveCap Ptest Ecompare cost ht hD hcap htest hcompare hcost
  exact hbound ht hD hcap htest hcompare hcost

end Erdos3.VectorPolynomial

end

end OAI

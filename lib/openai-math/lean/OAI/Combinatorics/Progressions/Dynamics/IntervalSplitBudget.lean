import OAI.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval

namespace OAI

section

namespace Erdos3

theorem mixedErrorPairBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    mixedErrorPairBudget p ≤ mixedErrorPairBudget q := by
  unfold mixedErrorPairBudget productNiltestBudget productObservableLipBudget
  gcongr

theorem mixedErrorBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    mixedErrorBudget p ≤ mixedErrorBudget q := by
  exact mixedErrorPairBudget_mono (hp.trans (le_mixedErrorPairBudget hp))
    (mixedErrorPairBudget_mono hp hpq)

def intervalErrorBaseBudget (p : ℝ) : ℝ := mixedErrorBudget (p + 2) + p + 2

def intervalErrorBudget (p : ℝ) : ℝ := mixedErrorPairBudget (intervalErrorBaseBudget p)

theorem intervalErrorBaseBudget_bounds {p : ℝ} (hp : 0 ≤ p) :
    2 ≤ intervalErrorBaseBudget p ∧ p ≤ intervalErrorBaseBudget p ∧
      mixedErrorBudget (p + 2) ≤ intervalErrorBaseBudget p := by
  have hp2 : 0 ≤ p + 2 := by linarith
  have hpair := hp2.trans (le_mixedErrorPairBudget hp2)
  have hglobal : 0 ≤ mixedErrorBudget (p + 2) := hpair.trans (le_mixedErrorPairBudget hpair)
  unfold intervalErrorBaseBudget
  constructor
  · linarith only [hp, hglobal]
  constructor <;> linarith only [hp, hglobal]

theorem exists_interval_error_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → intervalErrorBudget p ≤ (p + C) ^ C := by
  obtain ⟨a, _, ha⟩ := exists_mixed_error_budget
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + 2 + Polynomial.C a) ^ a + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Y + Polynomial.C a) ^ a)
  refine ⟨C, hC, fun p hp => ?_⟩
  have hbase := intervalErrorBaseBudget_bounds hp
  have hbase0 : 0 ≤ intervalErrorBaseBudget p := le_trans (by norm_num) hbase.1
  have hbound : intervalErrorBaseBudget p ≤ (p + 2 + a) ^ a + p + 2 := by
    unfold intervalErrorBaseBudget
    gcongr
    exact (ha (p + 2) (by linarith)).2
  have hpoly : ((p + 2 + a) ^ a + p + 2 + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Y, Polynomial.eval₂_pow] using hbudget p hp
  have hmono : (intervalErrorBaseBudget p + a) ^ a ≤
      ((p + 2 + a) ^ a + p + 2 + a) ^ a := by gcongr
  exact (ha _ hbase0).1.trans (hmono.trans hpoly)

end Erdos3

end

section

namespace Erdos3

def intervalSplitInput (K : ℝ) : ℝ := 2 * K + 2 * intervalErrorBudget K + 2

def intervalSplitTermBudget (c : ℕ) (K : ℝ) : ℝ := (intervalSplitInput K + c) ^ c

def intervalSplitLocalBudget (c : ℕ) (K : ℝ) : ℝ :=
  mixedErrorPairBudget (intervalErrorBudget K + intervalSplitTermBudget c K + 2)

theorem intervalErrorBudget_nonneg {K : ℝ} (hK : 0 ≤ K) : 0 ≤ intervalErrorBudget K := by
  have hb : 0 ≤ intervalErrorBaseBudget K := le_trans (by norm_num) (intervalErrorBaseBudget_bounds hK).1
  exact hb.trans (le_mixedErrorPairBudget hb)

theorem intervalSplitInput_bounds {K : ℝ} (hK : 0 ≤ K) :
    2 ≤ intervalSplitInput K ∧ K ≤ intervalSplitInput K ∧
      2 * K ≤ intervalSplitInput K ∧ 2 * intervalErrorBudget K ≤ intervalSplitInput K := by
  have hL := intervalErrorBudget_nonneg hK
  unfold intervalSplitInput
  constructor
  · linarith only [hK, hL]
  constructor
  · linarith only [hK, hL]
  constructor <;> linarith only [hK, hL]

end Erdos3

end

end OAI

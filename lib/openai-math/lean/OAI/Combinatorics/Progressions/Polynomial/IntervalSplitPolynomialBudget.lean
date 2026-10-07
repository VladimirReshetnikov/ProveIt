import OAI.Combinatorics.Progressions.Dynamics.IntervalSplitBudget

namespace OAI

section

namespace Erdos3

theorem exists_interval_split_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ K : ℝ, 0 ≤ K →
      2 * K + intervalSplitTermBudget c K ≤ (K + C) ^ C ∧
      intervalSplitLocalBudget c K ≤ (K + C) ^ C := by
  obtain ⟨a, _, ha⟩ := exists_interval_error_budget
  obtain ⟨b, _, hb⟩ := exists_mixed_error_budget
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C a) ^ a
  let V := (2 * X + 2 * Y + 2 + Polynomial.C c) ^ c
  let Z := (Y + V + 2 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * X + V + Z)
  refine ⟨C, hC, fun K hK => ?_⟩
  have hL : 0 ≤ intervalErrorBudget K := intervalErrorBudget_nonneg hK
  have hI : 0 ≤ intervalSplitInput K := le_trans (by norm_num) (intervalSplitInput_bounds hK).1
  have hF : 0 ≤ intervalSplitTermBudget c K := by unfold intervalSplitTermBudget; positivity
  have hi : intervalSplitInput K ≤ 2 * K + 2 * (K + a) ^ a + 2 := by
    unfold intervalSplitInput
    gcongr
    exact ha K hK
  have hv : intervalSplitTermBudget c K ≤ (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c := by
    unfold intervalSplitTermBudget
    gcongr
  have hm : 0 ≤ intervalErrorBudget K + intervalSplitTermBudget c K + 2 := by positivity
  have hz : intervalSplitLocalBudget c K ≤
      ((K + a) ^ a + (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c + 2 + b) ^ b := by
    apply (hb _ hm).1.trans
    gcongr
    exact ha K hK
  have hZ : 0 ≤ ((K + a) ^ a + (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c + 2 + b) ^ b := by
    positivity
  have hbound : 2 * K + (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c +
      ((K + a) ^ a + (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c + 2 + b) ^ b ≤ (K + C) ^ C := by
    simpa [X, Y, V, Z, Polynomial.eval₂_pow] using hbudget K hK
  constructor
  · linarith only [hv, hZ, hbound]
  · have hv0 : 0 ≤ (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c := by positivity
    linarith only [hz, hK, hv0, hbound]

end Erdos3

end

end OAI

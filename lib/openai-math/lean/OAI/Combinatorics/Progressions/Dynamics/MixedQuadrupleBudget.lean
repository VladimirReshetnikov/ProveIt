import OAI.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval

namespace OAI

section

namespace Erdos3

theorem exists_native_mixed_reduction_data (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      Nonempty (NativeMixedReductionData V ((p + C) ^ C)) := by
  obtain ⟨a, _, htranslation⟩ := NativeMultidegreeNilcharacter.exists_mixed_translation_equivalence s
  obtain ⟨b, _, hlower⟩ := NativeMultidegreeNilcharacter.exists_mixed_remainder_expansion s
  obtain ⟨c, _, hquad⟩ := NativeMultidegreeNilcharacter.exists_mixed_parallelogram_expansion s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + (X + Polynomial.C b) ^ b + (X + Polynomial.C c) ^ c + 2)
  refine ⟨C, hC, ?_⟩
  intro p V
  have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have ha : 0 ≤ (p + a) ^ a := by positivity
  have hb : 0 ≤ (p + b) ^ b := by positivity
  have hc : 0 ≤ (p + c) ^ c := by positivity
  have hs : (p + a) ^ a + (p + b) ^ b + (p + c) ^ c + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨{
    budget_two := by linarith only [ha, hb, hc, hs]
    translation := (htranslation V).mono (by linarith only [hb, hc, hs])
    lower := fun h δ j => (Classical.choice (hlower V h δ j)).mono (by linarith only [ha, hc, hs])
    parallelogram := fun k => (Classical.choice (hquad V k)).mono (by linarith only [ha, hb, hs]) }⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_mixed_quadruple_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      ∃ P : ℝ, Nonempty (NativeMixedReductionData V P) ∧
        7 * P ≤ (p + C) ^ C ∧ mixedErrorPairBudget P ≤ (p + C) ^ C ∧
        mixedErrorBudget P ≤ (p + C) ^ C := by
  obtain ⟨a, _, hdata⟩ := exists_native_mixed_reduction_data s
  obtain ⟨b, _, herror⟩ := exists_mixed_error_budget
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (7 * Y + (Y + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p V
  have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let P := (p + a) ^ a
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hE : 0 ≤ (P + b) ^ b := by positivity
  have hb : 7 * P + (P + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Y, P, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨P, hdata V, ?_, ?_, ?_⟩
  · linarith only [hb, hE]
  · exact (herror P hP).1.trans (by linarith only [hb, hP])
  · exact (herror P hP).2.trans (by linarith only [hb, hP])

end Erdos3

end

end OAI

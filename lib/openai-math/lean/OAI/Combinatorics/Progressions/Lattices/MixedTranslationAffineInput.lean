import OAI.Combinatorics.Progressions.Geometry.MixedEvaluationCoordinates

namespace OAI

section

namespace Erdos3

def mixedTranslationSlope (s : ℕ) : Option (ReplicatedIndex (mixedCorrelationDegree s)) → ℤ
  | none => 0
  | some j => if j.1 = 1 then 1 else 0

def mixedTranslationIntercept (s : ℕ) (h δ : ℤ) :
    Option (ReplicatedIndex (mixedCorrelationDegree s)) → ℤ
  | none => δ
  | some j => if j.1 = 1 then 0 else h

theorem mixedTranslationSample_affine (s : ℕ) (h n δ : ℤ) :
    (fun j => mixedTranslationIntercept s h δ j + mixedTranslationSlope s j * n) =
      mixedTranslationSample s ![h, n, δ] := by
  funext j
  rcases j with _ | ⟨j, k⟩
  · simp [mixedTranslationIntercept, mixedTranslationSlope, mixedTranslationSample]
  · fin_cases j <;> simp [mixedTranslationIntercept, mixedTranslationSlope,
      mixedTranslationSample, correlationInput]
    rfl

theorem mixedTranslationSlope_replaced_none (s : ℕ) (i : ReplicatedIndex (mixedCorrelationDegree s)) :
    mixedTranslationSlope s (coordinateReplaceIndex i none) = 0 := by
  simp [coordinateReplaceIndex, mixedTranslationSlope]

theorem mixedTranslationSlope_replaced_vanishes (s : ℕ)
    (i j : ReplicatedIndex (mixedCorrelationDegree s))
    (hj : j ∉ (mixedEvaluationCoordinates s).erase i) :
    mixedTranslationSlope s (coordinateReplaceIndex i (some j)) = 0 := by
  by_cases hji : j = i
  · simp [coordinateReplaceIndex, hji, mixedTranslationSlope]
  · have hj₁ : j.1 ≠ 1 := by
      intro h
      exact hj (Finset.mem_erase.mpr ⟨hji, (mem_mixedEvaluationCoordinates s j).mpr h⟩)
    simp [coordinateReplaceIndex, hji, mixedTranslationSlope, hj₁]

end Erdos3

end

end OAI

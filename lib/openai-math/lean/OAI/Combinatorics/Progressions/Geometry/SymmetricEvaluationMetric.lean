import OAI.Combinatorics.Progressions.Estimates.MomentEvaluationBounds
import OAI.Combinatorics.Progressions.Estimates.SymmetricEvaluationLowerBound

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

def symmetricEvaluationLip (m : ℕ) (K : ℝ≥0) : ℝ≥0 :=
  m * ((momentWeightBound m : ℝ≥0) * K) * (momentWeightBound m : ℝ≥0) ^ m

theorem symmetricEvaluation_metric {m : ℕ} {I X : Type*} [PseudoMetricSpace X]
    (f : Fin m → I → X → ℂ) {K : ℝ≥0}
    (hf : ∀ i j, LipschitzWith K (f i j)) (hn : ∀ i j x, ‖f i j x‖ ≤ 1)
    (k : SymmetricEvaluationIndex m I) :
    (∀ x, ‖symmetricEvaluation (fun i j => f i j x) k‖ ≤ (momentWeightBound m : ℝ) ^ m) ∧
      LipschitzWith (symmetricEvaluationLip m K)
        (fun x => symmetricEvaluation (fun i j => f i j x) k) := by
  have hB : (1 : ℝ≥0) ≤ momentWeightBound m := by exact_mod_cast momentWeightBound_pos m
  have h := bounded_lipschitz_fintype_prod
    (fun i x => momentLinear (fun j => f i (k.1 j) x) k.2) hB
    (fun i => momentLinear_lipschitz _ (fun j => hf i (k.1 j)) k.2)
    (fun i x => by simpa only [mul_one, NNReal.coe_natCast] using
      norm_momentLinear_le (fun j => f i (k.1 j) x) k.2 zero_le_one (fun j => hn i (k.1 j) x))
  simpa only [Fintype.card_fin, symmetricEvaluationLip, NNReal.coe_natCast,
    symmetricEvaluation, momentProduct, momentLinear] using h

end Erdos3

end

end OAI

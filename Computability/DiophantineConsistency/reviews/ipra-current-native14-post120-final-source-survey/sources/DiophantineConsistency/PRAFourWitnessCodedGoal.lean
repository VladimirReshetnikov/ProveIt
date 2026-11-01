import DiophantineConsistency.HerbrandFixedGoalExtractionBound
import DiophantineConsistency.PRAStageCodedRemoval
set_option autoImplicit false
namespace DiophantineConsistency.PRAFourWitnessCodedGoal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAUniversalCandidate PRAUniversalEquivalence
  PRAStageCodedChi PRAStageCodedRemoval HerbrandFourTriplePrenexAdapter HerbrandFixedGoalWeakening
  HerbrandFixedGoalExtractionBound

/-- The concrete four-witness coded χ premise entails the candidate-PRA
existential goal. The induction-proof-to-premise reduction is not assumed. -/
theorem PRA_proves_goal {m : ℕ} (pred : Code (m+3)) (θ : Semiproposition language 1)
    (hθ : θ.Open)
    (p : UniversalAxiom ⊢
      (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (sourceMatrix (chiMatrix pred) (liftGoal θ))))))))).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  let r := max m (max θ.fvSup ((chiMatrix pred).fvSup))
  have hm : m ≤ r := Nat.le_max_left _ _
  have hθr : θ.fvSup ≤ r := le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hβr : (chiMatrix pred).fvSup ≤ r := le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  obtain ⟨n,hn,_⟩ := extractBound r θ (chiMatrix pred) hθ (chiMatrix_open pred) p
  exact PRA_proves_codedGoal_of_stages r n pred θ hθ hθr hβr hm (candidate_proves_universal hn)
end DiophantineConsistency.PRAFourWitnessCodedGoal

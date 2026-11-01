import DiophantineConsistency.PRAOneInductionPremise
set_option autoImplicit false
namespace DiophantineConsistency.PRAOneInductionCandidateTransfer
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAUniversalCandidate PRAUniversalEquivalence
  PRAStageCodedInduction PRAOneInductionPremise

/-- The universal presentation remains strong enough when the same sentence
is adjoined to each presentation. -/
theorem universal_proves_candidate_plus (σ τ : Sentence language)
    (p : (PRA ∪ {σ}) ⊢ τ) : (UniversalAxiom ∪ {σ}) ⊢ τ := by
  letI : 𝗘𝗤 language ⪯ (UniversalAxiom ∪ {σ}) :=
    Entailment.WeakerThan.ofSubset (fun φ h => Or.inl (UniversalAxiom.equality φ h))
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M hM0 hM hEq hBoth
  letI : M↓[language] ⊧* UniversalAxiom := by
    constructor
    intro φ hφ
    exact hBoth.models _ (Or.inl hφ)
  have hCandidate : M↓[language] ⊧* PRA := modelCandidatePRA
  have hPlus : M↓[language] ⊧* (PRA ∪ {σ}) := by
    constructor
    intro φ hφ
    rcases hφ with h | h
    · exact hCandidate.models _ h
    · exact hBoth.models _ (Or.inr h)
  exact models_of_provable hPlus p

/-- Eliminate one closed coded Σ₁ induction axiom from a candidate-PRA proof
of an open-matrix existential goal. -/
theorem PRA_proves_goal_of_candidate_plus_one (pred : Code (0+3))
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ { (inductionFormula pred).univCl }) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  apply PRA_proves_goal_of_one_axiom pred θ hθ
  exact universal_proves_candidate_plus _ _ p
end DiophantineConsistency.PRAOneInductionCandidateTransfer

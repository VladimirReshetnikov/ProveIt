import DiophantineConsistency.PRAOneInductionCandidateTransfer
import DiophantineConsistency.PRAStageInductionSchema
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAFoundationOneInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAStageCodedInduction PRAStageInductionSchema
  PRAOneInductionCandidateTransfer

/-- Replace the one actual Foundation successor-induction axiom by its coded
counterexample-dual formulation, preserving an actual candidate-PRA proof. -/
theorem candidate_proves_with_coded_axiom (pred : Code 3) (τ : Sentence language)
    (p : (PRA ∪ {(succInd (codedSigma pred)).univCl}) ⊢ τ) :
    (PRA ∪ {(inductionFormula pred).univCl}) ⊢ τ := by
  letI : 𝗘𝗤 language ⪯ (PRA ∪ {(inductionFormula pred).univCl}) :=
    Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M hM0 hM hEq hBoth
  letI : M↓[language] ⊧* PRA := by
    constructor
    intro φ hφ
    exact hBoth.models _ (Or.inl hφ)
  have hcoded : M↓[language] ⊧ (inductionFormula pred).univCl := hBoth.models _ (Or.inr rfl)
  have hactual : M↓[language] ⊧ (succInd (codedSigma pred)).univCl := by
    have h := (modelClosedInduction_iff (M := M) pred).mp
    simpa [models_iff] using h (by simpa [models_iff] using hcoded)
  have hPlus : M↓[language] ⊧* (PRA ∪ {(succInd (codedSigma pred)).univCl}) := by
    constructor
    intro φ hφ
    rcases hφ with h | h
    · exact (inferInstance : M↓[language] ⊧* PRA).models _ h
    · simp only [Set.mem_singleton_iff] at h
      subst φ
      exact hactual
  exact models_of_provable hPlus p

/-- Eliminate one actual Foundation successor-induction instance for a coded
Σ₁ predicate with no external predicate parameters. -/
theorem PRA_proves_goal_of_succInd (pred : Code 3) (θ : Semiproposition language 1)
    (hθ : θ.Open)
    (p : (PRA ∪ {(succInd (codedSigma pred)).univCl}) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  apply PRA_proves_goal_of_candidate_plus_one pred θ hθ
  exact candidate_proves_with_coded_axiom pred _ p
end DiophantineConsistency.PRAFoundationOneInduction

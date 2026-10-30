import DiophantineConsistency.PRAFiniteInductionTagCodes
import DiophantineConsistency.PRATwoInductionTagged
/-! Eliminate any finite list of coded induction predicates ignoring c. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAFiniteParameterFreeInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAStageCodedInduction PRAOneInductionCandidateTransfer
  PRATwoInductionTagCodes PRAFiniteInductionTagCodes PRATwoInductionTagged

/-- One closed induction axiom for each member, with no external or c parameter. -/
def inductionAxioms (fs : List (Code 2)) : Theory language :=
  {σ | ∃ f ∈ fs, σ = (inductionFormula (liftTwo f)).univCl}

/-- A single tagged coded induction axiom supplies all the list's instances. -/
theorem candidate_proves_with_finite_dispatch (fs : List (Code 2)) (τ : Sentence language)
    (p : (PRA ∪ inductionAxioms fs) ⊢ τ) :
    (PRA ∪ {(inductionFormula (dispatch fs)).univCl}) ⊢ τ := by
  letI : 𝗘𝗤 language ⪯ (PRA ∪ {(inductionFormula (dispatch fs)).univCl}) :=
    Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hBoth
  letI : M↓[language] ⊧* PRA := by
    constructor
    intro σ hσ
    exact hBoth.models _ (Or.inl hσ)
  have hc : M↓[language] ⊧ (inductionFormula (dispatch fs)).univCl := hBoth.models _ (Or.inr rfl)
  have hPlus : M↓[language] ⊧* (PRA ∪ inductionAxioms fs) := by
    constructor
    intro σ hσ
    rcases hσ with hσ | hσ
    · exact (inferInstance : M↓[language] ⊧* PRA).models _ hσ
    · obtain ⟨f,hf,rfl⟩ := hσ
      obtain ⟨i,hi⟩ := List.get_of_mem hf
      have heq : PRA ⊢ PRATwoInductionTagged.substitutionEquation (dispatch fs) (liftTwo f) (tagCode i.val) := by
        rw [←hi]
        exact PRA_proves_dispatch_substitution fs i
      exact modelInductionOfSubstitution (dispatch fs) (liftTwo f) (tagCode i.val) heq hc
  exact models_of_provable hPlus p

/-- Any finite list of parameter-free coded induction instances can be
eliminated from a proof of an open-existential goal. -/
theorem PRA_proves_goal_of_finite_parameterFree (fs : List (Code 2))
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ inductionAxioms fs) ⊢ (∃⁰ θ).univCl) : PRA ⊢ (∃⁰ θ).univCl := by
  apply PRA_proves_goal_of_candidate_plus_one (dispatch fs) θ hθ
  exact candidate_proves_with_finite_dispatch fs _ p
end DiophantineConsistency.PRAFiniteParameterFreeInduction

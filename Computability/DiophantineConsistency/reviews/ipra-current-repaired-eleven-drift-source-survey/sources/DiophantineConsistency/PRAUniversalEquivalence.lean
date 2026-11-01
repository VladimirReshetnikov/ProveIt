import DiophantineConsistency.PRAUniversalInduction

/-! Deductive equivalence of the candidate theory and its proposed universal axioms. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAUniversalEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAUniversalCandidate PRAUniversalInduction

instance : 𝗘𝗤 language ⪯ UniversalAxiom :=
  Entailment.WeakerThan.ofSubset (fun σ h => UniversalAxiom.equality σ h)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* UniversalAxiom]

theorem modelCandidatePRA : M↓[language] ⊧* PRA := by
  constructor
  intro σ hσ
  rcases hσ with (((hEq | hDef) | hInd) | hBasic)
  · exact Theory.models (T := UniversalAxiom) M (UniversalAxiom.equality σ hEq)
  · exact Theory.models (T := UniversalAxiom) M (UniversalAxiom.defining σ hDef)
  · rcases hInd with ⟨φ, hφ, rfl⟩
    exact modelOpenInductionAxiom φ hφ
  · exact Theory.models (T := UniversalAxiom) M (UniversalAxiom.basic σ hBasic)

end models

/-- Every candidate-PRA theorem has a proof from the proposed universal axioms. -/
theorem universal_proves_candidate {σ : Sentence language} (h : PRA ⊢ σ) :
    UniversalAxiom ⊢ σ := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact models_of_provable (modelCandidatePRA (M := M)) h

/-- Every theorem from the proposed universal axioms has a candidate-PRA proof. -/
theorem candidate_proves_universal {σ : Sentence language} (h : UniversalAxiom ⊢ σ) :
    PRA ⊢ σ := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  have hU : M↓[language] ⊧* UniversalAxiom := by
    constructor
    intro τ hτ
    exact models_of_provable (inferInstance : M↓[language] ⊧* PRA) (PRA_proves_universalAxiom hτ)
  exact models_of_provable hU h

/-- The two explicit candidate presentations prove the same sentences. -/
theorem provable_iff (σ : Sentence language) : UniversalAxiom ⊢ σ ↔ PRA ⊢ σ :=
  ⟨candidate_proves_universal, universal_proves_candidate⟩

end DiophantineConsistency.PRAUniversalEquivalence

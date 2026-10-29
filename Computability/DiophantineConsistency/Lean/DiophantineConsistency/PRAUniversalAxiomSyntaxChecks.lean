import DiophantineConsistency.PRAUniversalAxiomSyntax

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
  DiophantineConsistency.PRAUniversalCandidate DiophantineConsistency.PRAUniversalSyntax
  DiophantineConsistency.PRAUniversalAxiomSyntax

example (σ : Sentence language) (h : UniversalAxiom σ) : UniversalPrefix σ := universalAxiom_isUniversal h
example : ∃ T : Theory language, (∀ σ, T σ → UniversalPrefix σ) ∧
    (∀ σ, T ⊢ σ ↔ PRA ⊢ σ) := candidate_has_universal_presentation
#print axioms DiophantineConsistency.PRAUniversalAxiomSyntax.universalAxiom_isUniversal
#print axioms DiophantineConsistency.PRAUniversalAxiomSyntax.candidate_has_universal_presentation
#check DiophantineConsistency.PRAUniversalAxiomSyntax.candidate_has_universal_presentation

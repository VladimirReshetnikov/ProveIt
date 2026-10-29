import DiophantineConsistency.PRAUniversalEquivalence

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
  DiophantineConsistency.PRAUniversalCandidate DiophantineConsistency.PRAUniversalEquivalence

example (σ : Sentence language) : UniversalAxiom ⊢ σ ↔ PRA ⊢ σ := provable_iff σ
#print axioms DiophantineConsistency.PRAUniversalEquivalence.modelCandidatePRA
#print axioms DiophantineConsistency.PRAUniversalEquivalence.universal_proves_candidate
#print axioms DiophantineConsistency.PRAUniversalEquivalence.candidate_proves_universal
#print axioms DiophantineConsistency.PRAUniversalEquivalence.provable_iff
#check DiophantineConsistency.PRAUniversalEquivalence.provable_iff

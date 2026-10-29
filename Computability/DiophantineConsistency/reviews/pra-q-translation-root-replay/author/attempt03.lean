import DiophantineConsistency.PRAQProofTranslation

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
  DiophantineConsistency.PRAQProofTranslation

example (σ : Sentence ℒₒᵣ) (h : RobinsonQ ⊢ σ) :
    PRA ⊢ Semiformula.lMap embedding σ := PRA_proves_qTheorem h
#print axioms DiophantineConsistency.PRAQProofTranslation.PRA_proves_qTheorem
#check DiophantineConsistency.PRAQProofTranslation.PRA_proves_qTheorem

import DiophantineConsistency.PRAQOrder

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
  DiophantineConsistency.PRAQCompatibility DiophantineConsistency.PRAQOrder

example : PRA ⊢ Semiformula.lMap embedding qLtDef := PRA_proves_qLtDef
example (σ : Sentence ℒₒᵣ) (h : RobinsonQ σ) :
    PRA ⊢ Semiformula.lMap embedding σ := PRA_proves_all_Q h
example : RobinsonQ qLtDef := RobinsonQ.ltDef

#print axioms DiophantineConsistency.PRAQOrder.modelLtWitness
#print axioms DiophantineConsistency.PRAQOrder.PRA_proves_qLtDef
#print axioms DiophantineConsistency.PRAQOrder.PRA_proves_all_Q
#check DiophantineConsistency.PRAQOrder.PRA_proves_all_Q

import DiophantineConsistency.PRAQOrderWitness

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
  DiophantineConsistency.PRAQOrderWitness

example : PRA ⊢ witnessSentence := PRA_proves_orderWitness
#print axioms DiophantineConsistency.PRAQOrderWitness.modelWitness
#print axioms DiophantineConsistency.PRAQOrderWitness.PRA_proves_orderWitness
#check DiophantineConsistency.PRAQOrderWitness.PRA_proves_orderWitness

import DiophantineConsistency.PRAQOrderWitnessCode

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
  DiophantineConsistency.PRAQOrderWitnessCode

example : PRA ⊢ codeWitnessSentence := PRA_proves_orderWitnessCode
example : DiophantineConsistency.PRAFiniteFunctionCodes.eval witnessCode
    (3 ::ᵥ 11 ::ᵥ List.Vector.nil) = 7 := by decide
#print axioms DiophantineConsistency.PRAQOrderWitnessCode.witnessCode_primrec
#print axioms DiophantineConsistency.PRAQOrderWitnessCode.eval_witnessCode
#print axioms DiophantineConsistency.PRAQOrderWitnessCode.PRA_proves_orderWitnessCode
#check DiophantineConsistency.PRAQOrderWitnessCode.PRA_proves_orderWitnessCode

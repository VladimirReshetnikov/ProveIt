import DiophantineConsistency.PRASelectCode

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
  DiophantineConsistency.PRATheory DiophantineConsistency.PRASelectCode

example : eval selectCode (0 ::ᵥ 7 ::ᵥ 5 ::ᵥ List.Vector.nil) = 5 := by decide
example : eval selectCode (1 ::ᵥ 7 ::ᵥ 5 ::ᵥ List.Vector.nil) = 7 := by decide
example : PRA ⊢ selectZeroSentence := PRA_proves_selectZero
example : PRA ⊢ selectSuccSentence := PRA_proves_selectSucc
#print axioms DiophantineConsistency.PRASelectCode.PRA_proves_selectZero
#print axioms DiophantineConsistency.PRASelectCode.PRA_proves_selectSucc
#print axioms DiophantineConsistency.PRASelectCode.modelSelectAmong

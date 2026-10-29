import DiophantineConsistency.PRAIsZero

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
  DiophantineConsistency.PRATheory DiophantineConsistency.PRAIsZero

example : PRA ⊢ isZeroCharacterSentence := PRA_proves_isZeroCharacter
example : eval isZeroCode (0 ::ᵥ List.Vector.nil) = 1 := by decide
example : eval isZeroCode (4 ::ᵥ List.Vector.nil) = 0 := by decide
#print axioms DiophantineConsistency.PRAIsZero.modelIsZeroCharacter
#print axioms DiophantineConsistency.PRAIsZero.PRA_proves_isZeroCharacter

import DiophantineConsistency.PRANonzeroCharacter

set_option autoImplicit false
namespace DiophantineConsistency.PRANonzeroCharacterChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRATheory PRANonzeroCharacter

example : PRA ⊢ nonzeroCharacterSentence := PRA_proves_nonzeroCharacter

#print axioms modelOneNeZero
#print axioms modelNonzeroCharacter
#print axioms modelNonzeroCharacterSentence
#print axioms PRA_proves_nonzeroCharacter
end DiophantineConsistency.PRANonzeroCharacterChecks

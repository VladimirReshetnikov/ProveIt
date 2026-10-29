import DiophantineConsistency.PRANonzero

set_option autoImplicit false
namespace DiophantineConsistency.PRANonzeroChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRATheory PRANonzero

example : PRA ⊢ nonzeroZeroSentence := PRA_proves_nonzeroZero
example : PRA ⊢ nonzeroSuccSentence := PRA_proves_nonzeroSucc

#print axioms modelNonzeroZero
#print axioms modelNonzeroSucc
#print axioms modelNonzeroZeroSentence
#print axioms modelNonzeroSuccSentence
#print axioms PRA_proves_nonzeroZero
#print axioms PRA_proves_nonzeroSucc
end DiophantineConsistency.PRANonzeroChecks

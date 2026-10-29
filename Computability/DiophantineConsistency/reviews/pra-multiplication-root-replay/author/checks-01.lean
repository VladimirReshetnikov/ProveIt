import DiophantineConsistency.PRAMultiplication

set_option autoImplicit false
namespace DiophantineConsistency.PRAMultiplicationChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRATheory PRAMultiplication

example : PRA ⊢ mulZeroSentence := PRA_proves_mulZero
example : PRA ⊢ mulSuccSentence := PRA_proves_mulSucc

#print axioms modelZero
#print axioms modelMulExpand
#print axioms modelMulZero
#print axioms modelMulSucc
#print axioms modelMulZeroSentence
#print axioms modelMulSuccSentence
#print axioms PRA_proves_mulZero
#print axioms PRA_proves_mulSucc
end DiophantineConsistency.PRAMultiplicationChecks

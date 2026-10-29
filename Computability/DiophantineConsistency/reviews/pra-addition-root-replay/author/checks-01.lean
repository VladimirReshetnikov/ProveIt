import DiophantineConsistency.PRAAddition

set_option autoImplicit false
namespace DiophantineConsistency.PRAAdditionChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRATheory PRAAddition

example : PRA ⊢ addZeroSentence := PRA_proves_addZero
example : PRA ⊢ addSuccSentence := PRA_proves_addSucc

#print axioms modelAddExpand
#print axioms modelAddZero
#print axioms modelAddSucc
#print axioms modelAddZeroSentence
#print axioms modelAddSuccSentence
#print axioms PRA_proves_addZero
#print axioms PRA_proves_addSucc
end DiophantineConsistency.PRAAdditionChecks

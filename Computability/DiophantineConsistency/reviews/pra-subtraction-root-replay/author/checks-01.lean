import DiophantineConsistency.PRASubtraction

set_option autoImplicit false
namespace DiophantineConsistency.PRASubtractionChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRATheory PRASubtraction

example : PRA ⊢ subZeroSentence := PRA_proves_subZero
example : PRA ⊢ subSuccSentence := PRA_proves_subSucc

#print axioms modelSubExpand
#print axioms modelSubZero
#print axioms modelSubSucc
#print axioms modelSubZeroSentence
#print axioms modelSubSuccSentence
#print axioms PRA_proves_subZero
#print axioms PRA_proves_subSucc
end DiophantineConsistency.PRASubtractionChecks

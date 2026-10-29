import DiophantineConsistency.PRAAddOne

set_option autoImplicit false
namespace DiophantineConsistency.PRAAddOneChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRATheory PRAAddOne

example : PRA ⊢ addOneSentence := PRA_proves_addOne

#print axioms modelComposition
#print axioms modelProjection
#print axioms modelBase
#print axioms modelStep
#print axioms modelAddOne
#print axioms PRA_proves_addOne
end DiophantineConsistency.PRAAddOneChecks

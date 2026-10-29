import DiophantineConsistency.PRAExhaustion

set_option autoImplicit false
namespace DiophantineConsistency.PRAExhaustionChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRATheory PRAExhaustion

example : exhaustionBody.Open := exhaustionBody_open
example : PRA ⊢ exhaustionSentence := PRA_proves_exhaustion

#print axioms exhaustionBody_open
#print axioms modelPredSucc
#print axioms body_eval
#print axioms modelExhaustion
#print axioms PRA_proves_exhaustion
end DiophantineConsistency.PRAExhaustionChecks

import DiophantineConsistency.PRAChallengePermutation
set_option autoImplicit false
namespace DiophantineConsistency.PRAChallengePermutationChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAChallengePermutation
example {n : ℕ} (q : Code (n+3)) : Code (n+3) := challengeFirst q
#print axioms modelChallengeFirst
#print axioms modelChallengeFirst_vector
#print axioms reorderedIndex_parameter
#print axioms reorderedIndex_challenge
end DiophantineConsistency.PRAChallengePermutationChecks

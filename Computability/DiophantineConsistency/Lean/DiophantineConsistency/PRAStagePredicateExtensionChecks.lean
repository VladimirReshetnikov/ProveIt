import DiophantineConsistency.PRAStagePredicateExtension
set_option autoImplicit false
namespace DiophantineConsistency.PRAStagePredicateExtensionChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRAStagePredicateExtension
example {m n : ℕ} (h : m ≤ n) (pred : Code (m+3)) : Code (n+3) := extendPredicate h pred
#print axioms modelExtendPredicate
#print axioms modelExtendedChi
end DiophantineConsistency.PRAStagePredicateExtensionChecks

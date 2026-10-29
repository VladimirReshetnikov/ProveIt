import DiophantineConsistency.ParsonsGuard
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsGuardChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsGuard

-- The substitution term and the side formula may both contain free parameters.
example {L : Language} (φ : Semiproposition L 1) (E : Proposition L)
    (t : SyntacticTerm L) : (guard φ E)/[t] = φ/[t] ⋎ E := guard_subst φ E t
example {L : Language} [L.LT] (φ : Semiproposition L 1) (E : Proposition L)
    (hφ : Hierarchy 𝚺 1 φ) (hE : Hierarchy 𝚺 1 E) :
    Hierarchy 𝚺 1 (guard φ E) := guard_sigma φ E hφ hE

#print axioms guard_subst
#print axioms guard_sigma
end DiophantineConsistency.ParsonsGuardChecks

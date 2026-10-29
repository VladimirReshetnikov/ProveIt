import DiophantineConsistency.ParsonsRule
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsRuleChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule

-- The client takes exactly the three indicated premises; the term and side
-- formula can contain arbitrary free parameters.
example {L : Language} [L.ORing] {T : Theory L} (φ : Semiproposition L 1)
    (E : Proposition L) (t : SyntacticTerm L) (hφ : Hierarchy 𝚺 1 φ)
    (hE : Hierarchy 𝚺 1 E) (hb : Proof T (base φ ⋎ E))
    (hs : Proof T (step φ ⋎ E)) (hn : Proof T (∼(φ/[t]) ⋎ E)) :
    Proof T E := three_disjunctions φ E t hφ hE hb hs hn

-- The guarded step is an actual first-order LK derivation, not an axiom.
example {L : Language} [L.ORing] (φ : Semiproposition L 1) (E : Proposition L) :
    Derivation [(step φ ⋎ E) 🡒 step (ParsonsGuard.guard φ E)] :=
  guard_step_logic φ E

#print axioms resolution
#print axioms prop_step
#print axioms guard_step_free
#print axioms guard_step_left
#print axioms guard_step_right
#print axioms guard_step_logic
#print axioms guard_result
#print axioms three_disjunctions
end DiophantineConsistency.ParsonsRuleChecks

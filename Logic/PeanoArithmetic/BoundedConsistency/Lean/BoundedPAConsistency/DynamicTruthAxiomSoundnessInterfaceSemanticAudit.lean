import BoundedPAConsistency.DynamicTruthAxiomSoundnessInterfaceSemantic

/-!
# Audit: reducing the axiom-soundness model-induction interfaces

The declarations below expose both unary invariants, their base and successor
cases, and the derivations of the two closure interfaces consumed by dynamic
PA-axiom soundness.  Each successor case names exactly the certificate law it
uses: the shift law for free-environment independence, and the universal
Tarski clause for the internally iterated quantifier block.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessInterfaceSemanticAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessInterfaceSemantic

#check FreeIndependenceInvariant
#check freeIndependenceInvariant_zero
#check freeIndependenceInvariant_succ
#check freeEnvironmentIndependence_of_invariant
#check ClosureInvariant
#check closureInvariant_zero
#check closureInvariant_succ
#check universalClosureIntroduction_of_invariant

#print axioms freeIndependenceInvariant_zero
#print axioms freeIndependenceInvariant_succ
#print axioms freeEnvironmentIndependence_of_invariant
#print axioms closureInvariant_zero
#print axioms closureInvariant_succ
#print axioms universalClosureIntroduction_of_invariant

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessInterfaceSemanticAudit

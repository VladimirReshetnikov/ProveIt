import BoundedPAConsistency.UniformInternalProvabilityTheorem

/-!
# Audit: the uniform internal provability theorem

This audit exposes the model-internal restricted-consistency proof selector,
its uniformity over all models of PA, and the resulting object theorem.  The
axiom listing of the headline theorem is the trust boundary of the entire
development: only Lean's three standard classical axioms may appear.
-/

namespace LeanProofs.BoundedPAConsistency.UniformInternalProvabilityTheoremAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.UniformInternalProvabilityTheorem

#check @paRestrictedConsistencyProofSelectorIn_compiled
#check @paRestrictedConsistencyProofSelectorInAllModels_compiled
#check @pa_proves_uniformRestrictedConsistencyProvability

#print axioms paRestrictedConsistencyProofSelectorIn_compiled
#print axioms paRestrictedConsistencyProofSelectorInAllModels_compiled
#print axioms pa_proves_uniformRestrictedConsistencyProvability

end LeanProofs.BoundedPAConsistency.UniformInternalProvabilityTheoremAudit

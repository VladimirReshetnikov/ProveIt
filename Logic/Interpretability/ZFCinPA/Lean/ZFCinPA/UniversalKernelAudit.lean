import ZFCinPA.UniversalKernel

/-!
# Audit for the universal proof kernels

The audit keeps the interface boundary visible: a kernel stores one
represented implication proof, its combinators are Hilbert-level plumbing,
and the only substantive constructor is the ω-induction wrapper, whose
mathematical content is `SeparationKernel`'s fixed compiled source
derivation.  No induction recognizer and no `shiftFixed` field survive into
the public interface.
-/

namespace LeanProofs.ZFCinPA.UniversalKernelAudit

open LeanProofs.ZFCinPA

/-! ## The kernel interface -/

#check @UniversalKernel
#check @UniversalKernel.compile
#check @UniversalKernel.ofUniversalProof
#check @UniversalKernel.recontextualize

/-! ## Cheap transports -/

#check @UniversalKernel.ofEq
#check @UniversalKernel.ofEq_predicate
#check @UniversalKernel.withPredicate
#check @UniversalKernel.withPredicate_predicate

/-! ## The ω-induction constructor -/

#check @UniversalKernel.ofOmegaInduction
#check @UniversalKernel.ofOmegaInduction_predicate
#check @UniversalKernel.ofOmegaInductionProofs

/-! ## Assumption audit

Foundation's arithmetic is classical, so `Classical.choice`, `propext` and
`Quot.sound` are expected; nothing beyond Lean's three standard axioms
should appear, and in particular no `sorry` and no theory-specific axiom. -/

#print axioms UniversalKernel.compile
#print axioms UniversalKernel.recontextualize
#print axioms UniversalKernel.ofEq_predicate
#print axioms UniversalKernel.withPredicate_predicate
#print axioms UniversalKernel.ofOmegaInduction
#print axioms UniversalKernel.ofOmegaInductionProofs

end LeanProofs.ZFCinPA.UniversalKernelAudit

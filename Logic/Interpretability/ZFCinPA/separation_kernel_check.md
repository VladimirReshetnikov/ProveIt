# Checked internal Separation and omega induction

The unchanged [SeparationKernel source](Lean/ZFCinPA/SeparationKernel.lean)
passes a fresh Lean check and **22 axiom probes with 23 typed clients**,
with no warnings. The [actual record](results/separation-kernel-verification.json)
checks specialization of a standard finite proof template at an arbitrary
internally coded unary predicate in an IΣ₁ model. The predicate must be
well typed and fixed by free-variable shifting; its code need not be standard.

The resulting internal ZFC Separation proof supports
`zfcOmegaInductionOfShiftFixed`: internal proofs of the empty-set and
successor cases yield an internal proof for every object belonging to all
inductive sets. This intersection defines the source's von Neumann naturals. The result
does not identify those objects with external standard naturals. The compiler
handles standard finite source proofs with internal predicate substitutions;
it does not claim compilation of arbitrary internally coded source proofs.

Source and audit took 18.767 and 2.635 seconds under default proof limits,
one thread, 4,096 MiB and a shared 120-second deadline. All 98 recorded inputs
and the fresh first-provider object remained unchanged after the audit.
Every axiom report contains only standard Lean axioms.

The first attempt failed before elaboration because the sparse Foundation
namespace lacked `Basic.Misc`. The accepted second guard selects the exact
previously checked `Basic.Misc` and `Basic.Axioms` artifacts and companions.
Source and audit are unchanged. Nine project providers, five opaque cached
boundaries and Init are explicit; the complete cached namespace is not
attested. The reused predicate-template compiler retains its legacy replay
policy, ten prerequisite warnings and original capture limitations.

The [publication](results/separation-kernel-publication.json),
[history](separation-kernel/history.json.gz) and
[audit/API and guard-repair review](separation-kernel/peer-review.json)
retain the original import failure, both guards, raw logs and source snapshots.
The peer receipt predates the successful second execution. This check closes
one original validator inventory entry; it does not close the final
240-state consistency equivalence.

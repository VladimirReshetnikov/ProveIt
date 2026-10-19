# Checked universal proof kernels

The unchanged [UniversalKernel source](Lean/ZFCinPA/UniversalKernel.lean)
passes a fresh Lean check and **13 axiom probes with 15 typed clients**,
with no warnings. The [actual record](results/universal-kernel-verification.json)
checks the represented-proof interface used by the staged certificate
compiler: a unary predicate together with an internal proof that a context
implies its universal closure.

The interface specializes that proof at a context proof, changes contexts
by an internal implication, and transports contexts or predicates along
equalities. The ZFC-specific constructor uses the checked
[Separation/omega-induction kernel](separation_kernel_check.md). It retains
the shift-fixedness of the internally coded predicate and both internal
induction-premise proofs as inputs. Its conclusion is explicitly relativized
to von Neumann naturals, defined by membership in every inductive set.
No induction axiom for arbitrary set predicates or certificate successor
proof is introduced.

Source and audit took 2.816 and 3.052 seconds with default proof limits,
one thread, 4,096 MiB and a shared 120-second deadline. All 114 recorded
inputs and the fresh first-provider object remained unchanged after the
audit. Every probe uses only standard Lean axioms.

The actual SeparationKernel record supplies ten selected project providers,
five explicit opaque boundaries and Init. Its inherited predicate-template
compiler evidence, earlier warnings and legacy capture limits remain
recorded; this check rebuilds no dependencies and does not attest the entire
cache. The [publication](results/universal-kernel-publication.json) and
[history](universal-kernel/history.json.gz) preserve the reviews, audit,
guard and actual logs. The final PA composition remains pending.

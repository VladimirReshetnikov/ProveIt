# Checked compactness and completeness interfaces

[`Compactness`](Lean/FirstOrder/Compactness.lean) now has a fresh
[local Lean check](results/compactness-verification.json). It proves that a
sentence theory in the repository's fixed language of equality and one
binary relation has a model exactly when all its finite subtheories do.
Models include an assignment, so their carriers are nonempty. The proof
uses the existing Henkin completeness and soundness results.

The unchanged source passes three named axiom probes and three typed callers
with zero warnings. Source and audit took 0.270 and 0.234 seconds, using
default proof limits, one thread, 4,096 MiB and a shared 120-second deadline.
Three exact project source/object pairs and Init are reused from an accepted
check. No previously unverified Compactness object is imported, and no
dependency rebuild is performed.

[`ClassicalCompleteness`](Lean/FirstOrder/ClassicalCompleteness.lean) then
provides the finite-context and infinite-theory completeness interfaces,
model existence, and equivalence of consistency with having a model.
Finite contexts and target formulas may be open; infinite base theories keep
the explicit sentence hypothesis, and syntactic consequence records finite
axiom support. Its [actual check](results/classical-completeness-verification.json)
passes eight named probes and eight typed callers with zero warnings. Source
and audit took 0.288 and 0.243 seconds under the same resource policy,
reusing four project pairs and Init, including the newly checked Compactness.
All reported axioms in both runs are standard Lean axioms.

The [compactness publication](results/compactness-publication.json) and
[completeness publication](results/classical-completeness-publication.json)
preserve the source bindings, audits, provider guards, raw logs and
preparation history. These are prerequisites for the bounded-consistency
work; they supply no assertion that
ZFC is consistent or that the 240-state machine never halts.

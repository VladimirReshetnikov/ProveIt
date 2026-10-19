# Checked induction over internal proof packages

The unchanged [PackageInduction source](Lean/ZFCinPA/PackageInduction.lean)
passes a fresh Lean check and **six axiom probes with eight typed clients**,
with no warnings. The [actual record](results/package-induction-verification.json)
checks existential package induction at every index of an IΣ₁ model.

A Σ₁-definable package relation suffices if it has a base witness, every
package extends to a successor package, and each package yields a ZFC proof
of the indexed consistency code. Existentially forgetting the package uses
an explicit index/witness coordinate swap. Internal Σ₁ induction then covers
nonstandard indices as well as standard ones; packages need not be unique
or canonically selected. The direct specialization uses represented proofs
of a Σ₁-definable master code as packages.

These results retain the base, successor and extraction obligations as
hypotheses. They do not construct the certificate family or prove the
unconditional uniform selector or final PA comparison.

Source and audit took 1.932 and 1.922 seconds with default proof limits,
one thread, 4,096 MiB and a shared 120-second deadline. All 412 recorded
inputs and the fresh first-provider object remained unchanged after the
audit. Every probe uses only standard Lean axioms.

The actual [UniformStatement check](uniform_statement_check.md) supplies
38 selected project providers. Seven opaque boundaries and Init remain
explicit. The guard adds current-only companion observations for cached D1
and InductionSchemeDelta1, preserving their original source/object evidence
without claiming earlier companion captures or a complete cache check.

The [publication](results/package-induction-publication.json) and
[history](package-induction/history.json.gz) preserve the source/API review,
audit, guards and actual logs. The first guard stopped at an artifact-count
preflight check. The next reached Lean but failed at import because the
isolated tree omitted cached companion files. The final guard stages and
checks those files; source, audit and proof limits are unchanged. This closes
one original validator inventory entry.

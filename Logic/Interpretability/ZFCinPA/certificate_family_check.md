# Checked certificate assembly and exact consistency extraction

The unchanged [CertificateFamily source](Lean/ZFCinPA/CertificateFamily.lean)
passes a fresh Lean check and **20 axiom probes with 22 typed clients**,
with no warnings. The [actual record](results/certificate-family-verification.json)
checks the eight-field certificate assembly, its proof projections and its
Σ₁ code construction.

The family chooses seven fields; its eighth field is forced to be the exact
`conZFCSetCodeFun` value at the current internal index. Given a represented
proof of the assembled code, the module recovers the conclusion's
well-formedness from the derivation and projects out an internal ZFC proof
of that exact consistency code. This works at arbitrary internal indices
without assuming global well-formedness of the consistency-code builder.
The audit also calls the exact-value extraction directly.

Σ₁ definability of the seven field-code functions yields Σ₁ definability
of the full master code. The eighth graph is supplied by UniformStatement.
The construction retains the incoming certificate proof and field-graph
premises; it supplies neither a concrete family nor its base and successor
proofs.

Source and audit took 6.464 and 2.762 seconds with default resource limits,
one thread, 4,096 MiB and a shared 120-second deadline. The source's two
existing local transparency settings are retained; they identify the
internalized theory's definitional wrappers. All 428 recorded inputs and
the fresh first-provider object remained unchanged after the audit.
Every probe uses only standard Lean axioms.

The actual [PackageInduction check](package_induction_check.md) supplies
39 selected project providers, seven explicit opaque boundaries and Init.
Its separately recorded current-only D1 and induction companion observations
remain distinguished from the older evidence. No dependency rebuild or
complete cache check is claimed. The
[publication](results/certificate-family-publication.json) and
[history](certificate-family/history.json.gz) preserve the source/API review,
audit, guard and actual logs. This closes one original validator inventory
entry; the final binary-machine PA comparison remains pending.

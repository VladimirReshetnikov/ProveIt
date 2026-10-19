# Checked certificate-field code construction

The unchanged [CertificateFields source](Lean/ZFCinPA/CertificateFields.lean)
passes a fresh Lean check and **34 axiom probes with 34 typed clients**,
with no warnings. The [actual record](results/certificate-fields-verification.json)
checks all seven field-code graphs, their external sentence closedness and
their quotation identities at standard indices.

The seven fields describe local polarity laws, bounded decidedness, shift
and renaming invariance, bounded axiom truth, and the Tarski elimination
and introduction clauses. Each code builder has a Σ₁ graph at arbitrary
internal indices in every IΣ₁ model. At the cast of each external natural
number, it agrees exactly with the quotation of the corresponding finite
field sentence. The audit also checks the variable-slot bounds and the
quotation rules used when those fields are assembled.

This module constructs codes and proves syntactic identities. It does not
prove the field sentences true or internally provable, nor establish
well-formedness of their codes at arbitrary internal indices. The latter
is the next `ConcreteFamily` obligation. The forced eighth consistency
field belongs to [CertificateFamily](certificate_family_check.md); no
certificate proof or final PA endpoint is supplied by this check.

Source and audit took 42.610 and 3.106 seconds with one thread, 4,096 MiB
and a shared 120-second deadline. All existing source-local proof limits
were retained: 23 one-million-heartbeat bounds, one two-million bound,
the `fb08` four-million/100,000-recursion bound, and two final quotation
proofs' recursion bounds of 4,000. The audit uses default proof limits.
All 414 recorded inputs and the fresh first-provider object remained
unchanged after the audit. Every probe uses only standard Lean axioms.

The actual [LevelCodeTower check](level_code_tower_check.md) supplies 39
selected project providers, seven explicit opaque boundaries and Init.
All 398 immediate-parent inputs were rechecked; older capture limits and
separate current-only companion observations remain recorded. No dependency
rebuild or complete cache check is claimed. The
[publication](results/certificate-fields-publication.json) and
[history](certificate-fields/history.json.gz) preserve the source/API review,
original audit, focused audit, guard and actual logs. This closes one
original validator inventory entry.

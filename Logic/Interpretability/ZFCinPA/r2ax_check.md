# Checked validator proofs of internally coded collection axioms

The unchanged [R2Ax source](Lean/ZFCinPA/R2Ax.lean) passes a fresh Lean check
and **three axiom probes with four typed clients**. The
[actual record](results/r2ax-verification.json) checks the GIC body, arbitrary
internal universal closure, and every internal code recognized by `GicR`.
The environment is odd and the encoding stream even. Universal closure uses
Π₂ induction in a model of IΣ₁ and IΣ₂, so the binder count may be nonstandard.
Its body must be well typed and fixed by free-variable shifting.

This advances the translation from the native theory to validator proofs.
It does not yet cover every native axiom, the full reflection theorem or the
final binary-machine endpoint. All three reports use only standard Lean axioms.

Source and audit took 11.451 and 1.909 seconds under default proof limits,
one thread, 4,096 MiB and a shared 120-second deadline. The source retains
one unused-section-variable warning in the private `sigma1_to_pi2` lemma;
the audit has no warnings. All 531 recorded inputs and the fresh
first-provider object remained unchanged after the audit.

The initial source check passed, but the audit needed a `noncomputable`
section and the namespace that defines `OddEnv`. The successful second
attempt changes only those audit declarations. Both attempts, exact logs
and the unchanged source are preserved in the
[history](r2ax/history.json.gz) and bound by the
[publication](results/r2ax-publication.json).

The guard selects 93 project providers from the actual NativeTheory, R2Gic
and NativePeel results, with eleven retained opaque cached boundaries and
two toolchain providers. It distinguishes ten directly encountered opaque
boundaries from retained `HFS.Seq`, and direct Init from retained Omega.
Historical source warnings and capture limitations remain explicit.
NativePeel's selected accepted pairs are checked without claiming that its
entire historical input map still describes the current tree.

The [original source/API review](r2ax/peer-review.json) missed the two audit
setup requirements. The [successor review](r2ax/audit-v2-review.json) records
that correction and preserves the earlier receipt as historical evidence.
Neither static review substitutes for the successful actual run.

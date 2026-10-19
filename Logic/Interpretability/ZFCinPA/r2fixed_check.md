# Checked validator proofs of the fixed native axioms

The unchanged [R2Fixed source](Lean/ZFCinPA/R2Fixed.lean) passes a fresh Lean
check and **16 axiom probes with 16 typed clients**. The
[actual record](results/r2fixed-verification.json) checks the encoded equality
axioms, membership irreflexivity and the literal container axiom. The final
container theorem applies at arbitrary internally coded odd environments
and even encoding streams.

The intermediate container bridge retains the eight strict inequalities
between its nine labels. Its conclusion preserves the literal negated
existential and double-negation forms used by the encoder. The equality
and irreflexivity interfaces need IΣ₁; the container section retains the
source's declared IΣ₂ instance. This unit and the
[collection-axiom check](r2ax_check.md) supply individual axiom translations;
the later all-native-axiom and reflection interfaces remain separate checks.

Source and audit took 48.007 and 4.077 seconds with default proof limits,
one thread, 4,096 MiB and a shared 120-second deadline. Three source warnings
remain: one unused simplification argument and two unused IΣ₂ section
instances. The audit has no warnings. All 549 recorded inputs and the fresh
first-provider object remained unchanged. Every probe uses only standard
Lean axioms.

The first source compilation passed, but its audit lacked the namespace
defining the encoded `ex`, `neg` and `conj` operators. Unknown-name errors
were followed by typeclass errors and a default-heartbeat timeout. Adding
that namespace alone makes the second audit pass; neither theorem source
nor proof limits changed. An earlier unexecuted audit's separate `OddEnv`
namespace correction is also preserved.

The guard reuses the exact successful R2Ax result and checks all its current
recorded inputs. It selects 94 project providers, with eleven retained opaque
boundaries and two toolchain providers; direct and merely retained boundaries
are distinguished. The six selected Foundation module families retain their
captured companions. The [publication](results/r2fixed-publication.json) and
[history](r2fixed/history.json.gz) preserve every audit version, the failed
attempt, corrected guard, source snapshots and raw logs. This closes one
original validator inventory entry, without asserting the final PA endpoint.

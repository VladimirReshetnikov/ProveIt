# Closing internally many interpreted binders

[`NativePeel`](Lean/ZFCinPA/NativePeel.lean) turns a derivation of an opened
schema body, with its domain side formulas, into a derivation of its
interpreted universal closure. The binder count is an arbitrary element of
an IΣ₁ model. The theorem retains the explicit `Good` interpretation,
well-formedness and shift-invariance hypotheses and the remaining domain
side formulas. It does not assume that the interpreted domain is inhabited
or that any native theory axiom holds there.

The [fresh check](results/native-peel-verification.json) passes six named
axiom probes and eight typed callers with zero warnings. Source and audit
took 7.887 and 2.013 seconds, with default proof limits, one thread,
4,096 MiB and a shared 120-second deadline. All reported axioms are standard
Lean axioms.

The first source check found an extra explicit element argument in a call
to `domSet_succ_subset`, whose element binder is implicit. Removing that
argument is the entire source change; the theorem statements and audit are
unchanged. The [publication record](results/native-peel-publication.json)
and [history](native-peel/history.json.gz) retain the original source,
failed run and corrected successful run, including an earlier unexecuted
guard correction for historical theorem names.

The guard selects 13 exact project prerequisites, five external source/object
pairs and Init from the checked interpretation core and the historical
open-schema check. The latter record lacks modern first-provider and
pre-audit capture fields; the guard preserves that limitation and checks
the selected current pairs without claiming those fields existed. The
successful run's original canonical-source binding predates the one-line
publication repair and remains historical evidence. No dependency was
rebuilt and the complete Foundation namespace is not independently attested.

This closes the generic binder-peeling prerequisite. Native axiom transport,
validator consistency equivalence and the final binary240 PA theorem remain
separate checks.

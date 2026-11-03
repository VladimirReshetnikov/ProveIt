# Artifact audit: standard-iPRA quartic-40 author extension

The retained [author run](../../research/ipra-standard-qm40/author-rebuild/observations/attempt02/)
is consistent with its live artifacts at the time of this audit. All five
recorded compilation steps exited 0 and produced the recorded objects. The
last source states three derivability theorems in `standardTheory`: the
shifted symbolic 40-variable literal is equivalent to the negated mapped
refutation predicate; the Gödel–Gentzen image of the selected Foundation ZFC
consistency sentence is equivalent to that negation; and the two are
equivalent. The last log reports exactly those three theorem names, each with
`propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.

[`audit.py`](audit.py) checks the retained and live source snapshots, logs,
preflight, result and five step receipts; all 10 fixed inputs, five frozen
sources, 440 final direct-candidate guards and 240 inherited native-parent
guards; and the five output objects and absent companions. It checks that the
only changes to the 200 initial guards are those five outputs. For each
recorded direct import, it compares the source-declared import set with the
receipt and checks search order, matching object hashes, and the ten recorded
companion slots in all four searched roots. It verifies the exact three axiom
report names and sets. These are point-in-time checks before and after the
audit; the original `/tmp` artifacts are required to repeat them.

The `IPRAStandardTheory` compiler log contains three linter warnings. The
audit checks that the **complete** warning-bearing log equals the pinned
historical baseline after replacing only the source path, and that all four
standard-theory source snapshots have the exact hashes recorded in the pinned
historical state. No warning occurs in the other four logs. The normal audit
exited 0; optimized Python was rejected. This is not a blanket warning
allowlist and does not validate a changed source or changed diagnostics.

The run is a single-author extension over the previously built native/model
provider. Neither it nor this audit provides a matched peer replay or a fresh
authenticated project-transitive, package-transitive or dynamic-loading
closure; source and guard checks are sampled rather than continuous. The
direct-import comparison uses the recorded dependency query and does not
independently rerun Lean. The external literal/DAG comparison does not supply
formal semantics of a PDF or bind its bytes. The result is the standard
theory theorem for the symbolic literal on the recorded provider, subject to
those inherited boundaries.

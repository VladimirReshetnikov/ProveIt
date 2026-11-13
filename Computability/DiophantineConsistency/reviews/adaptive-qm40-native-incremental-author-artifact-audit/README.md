# Independent artifact audit: incremental quartic-40 native endpoint

The retained [author observation](../adaptive-qm40-native-incremental-author/README.md)
is internally consistent with the live build artifacts at the time of this
audit. Both native compilation steps report exit 0, and the checks log has
exactly the three named reports `sameNoZero40`, `bridge40`, and
`literal_equivalence`, each with `propext`, `Classical.choice`, and
`Quot.sound` and no `sorryAx`. The named native theorem is a derivability
statement in the repository's **native** iPRA theory, for the shifted symbolic
40-variable literal and its selected fixed ports.

[`audit.py`](audit.py) checks the hashes of the retained and live preflight,
result, step receipts and logs; the two output objects; all 23 recorded fixed
inputs, six native-source records, and 240 final direct-candidate guards,
including absences, symlink text and resolved paths. It verifies that the two
new `.olean` files are the only changes to the preflight guard set, that the
reported direct dependency sets and all ten companions in each of the four
searched roots are represented, and that present `.olean` candidates agree
with the selected first candidate. It also checks the individual step
receipts against `RESULT.json` and verifies the exact axiom report names and
sets. It checks point-in-time records before and after and rejects optimized
Python. The normal audit exited 0; the optimized invocation was rejected.

The runner checks direct dependency candidates and companions at sampled
boundaries. The six model objects come from the preceding author-only bounded
run; its historical provider and project-transitive, package-transitive,
dynamic-loading and between-snapshot limitations are inherited. This audit
did not execute Lean, observe the run continuously, authenticate that full
closure, or perform a matched peer replay. Its direct-candidate check relies
on the recorded dependency query, not a fresh independent dependency query.
It also requires the original `/tmp` artifacts to reproduce the live checks.

The source-level literal/DAG verifier is external to Lean and is not a
formal interpretation of a rendered PDF or its coefficient bytes. The
separate standard-presentation client and any subsequent retry or endpoint
require their own compilation and evidence; this audit does not establish
them.

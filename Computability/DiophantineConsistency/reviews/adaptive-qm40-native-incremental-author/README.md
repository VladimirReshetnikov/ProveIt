# Incremental author-side 40-variable native endpoint

Tool session `7352` exited 0 after compiling `IPRAQM40Native` and
`IPRAQM40NativeChecks` in a fresh overlay. The latter reports only `propext`,
`Classical.choice` and `Quot.sound` for the model comparison, bridge and
`literal_equivalence`, with no `sorryAx`. The final receipt, direct guards,
step records, compiler logs and the observed terminal result are retained
here; the live build is `/tmp/ipra-qm40-incremental-author-20261102-d`.

The theorem states, in the repository's native iPRA theory, that the shifted
40-variable fixed-port literal has no zero iff the selected Foundation ZFC
refutation predicate has no witness. Its model bridge is over arbitrary
IΣ₁ models and uses the six author-side model objects from the earlier
[bounded run](../adaptive-qm40-native-bounded-replay/README.md). That run's
native attempt timed out; a first incremental retry failed in dependency
resolution, as [recorded separately](../adaptive-qm40-incremental-shadow-failure/README.md).

This is a single-author incremental build, not a matched replay or a fully
authenticated current-source closure. The runner checks direct imports and
companions and their precedence at sampled points; the earlier model build's
project, package, transitive, dynamic and between-snapshot ancestry remains
inherited. The external literal verifier compares 166 source rows with the
pinned candidate graph; it is not a Lean interpretation of PDF bytes. A later
[standard-presentation client](../../research/ipra-standard-qm40/author-rebuild/README.md)
has compiled in a separate author-side extension.

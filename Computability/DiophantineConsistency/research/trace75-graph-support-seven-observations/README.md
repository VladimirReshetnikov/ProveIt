# Seven graph-support candidate observations

This read-only checker examines the seven local observation JSONs identified
by the [28-object triage](../trace75-graph-support-28-triage/README.md). For
each, it verifies the JSON hash, exactly one reported exit-0 session with the
matching source hash, the retained source and log hashes, the module's entry
in the JSON's object-hash table, the currently present `.olean` under the
reported overlay, and the final selected `.olean` hash. It records the two
current realpaths separately.

For five modules the currently resolved overlay and final paths are the
same: `CyclicAnyPhase`, `HighMaskLocal`, `SelectedBandWord`,
`TemporalCarryExact` and `TemporalSafeCyclic`. For `CleanGeometry` and
`CleanMaskClasses` they are different current realpaths with the same recorded
object hash. Complete paths, hashes and reported session numbers are in
attempt01 stdout.

These are separately reported successful source sessions and object-hash
observations. The JSONs do not atomically bind the hash to that exact session
or authenticate producer-time direct imports; current same realpath does not
prove the file was never replaced. The two different-realpath cases do not
prove a copy or producer relationship. Companion, upstream source/object,
package-transitive and dynamic ancestry and independent Lean replay remain
open; this does not change the endpoint's external-file boundary.

Author attempt01 exited 0 without invoking Lean. Checker SHA-256 is
`4fae7cdcde4465ef09b99ecfa954f80db26bd31c998de1b34e47a46fc8b194df`,
terminal SHA-256 is
`645fdb17a5b85f2baa76ea63797ce1e0e225922b25e0b9a4d51bff7d8cdb668a`,
and stdout SHA-256 is
`8f6360726fe0f1917da33d3914c91d09e30b9c71402a20d6758ad1aa5d9f03f9`.
The [independent observation audit](../../reviews/trace75-graph-support-seven-observations-independent/README.md)
rechecked the source/session/hash evidence and the five/two path
classification without asserting an atomic producer link.

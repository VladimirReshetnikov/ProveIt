# Independent audit of direct-BFS cell/reset v3 receipts

The captured read-only check passes for the corrected guarded author builds
of `DirectBFS80CellShift` and `DirectBFS80UniformReset`. It verifies source,
self-pinning v3 runner and Lean hashes; all listed selected object hashes;
logs and printed axiom targets; six retained terminal histories; and nine
sampled resource observations. It independently resolves all ten direct
imports, verifies each selected object is individually pinned, and compares
each resolved real path/hash to the v3 receipt's pre- and post-build direct
import snapshots. The snapshots agree. This is not a Lean replay or a full
serialized, transitive project/package, dynamic-library or historical
source-to-object ancestry audit.

The cell v3 run now explicitly pins its formerly omitted
`SymbolicKBandDraft.olean`. Its recorded resolved real path is
`/tmp/ipra-graph-band-pair-01/author/lib/DiophantineConsistency/SymbolicKBandDraft.olean`,
SHA-256 `90516e7b8ec94eb0f4b917979e0c2800c4e8b2c1c3362ea5131baa631415402f`.
This is the real-path target of the selected path under the pinned provider;
the [earlier audit](../direct-bfs-cell-and-80-source-data-independent/README.md)
recorded that provider-facing path after the prior run. The reset v3 run
selects the new cell object at
`/tmp/direct-bfs-80-cell-11aqwvq4/DirectBFS80CellShift.olean`. Both output
objects are bit-identical to the earlier accepted versions and the source
hashes match. The v3 snapshots authenticate the selected bytes at the
recorded pre/post checks; the old post-hoc hash does not retroactively
authenticate the original compile-time selection.

The cell theorem assumes an actual positive 80-graph zero and all four
direct-BFS symbolic port equalities. It reconciles the graph's radix lengths
and concludes indexed carry, bit alignment and a cell offset
`(E/67) % (8807*N) = 8807*s` with `s<N` at one N. The reset theorem joins
its support information at that same N, then proves zero temporal predecessor
digits and incoming carries at every in-range column congruent to 2195, 3296,
4393 or 5495; at the latter two columns it also proves the target temporal
digit is zero. The source uses the direct-BFS coefficient family and the
graph's own residual power. No complete direct decoder, machine/color
conjugacy, whole-graph equivalence, external JSON/PDF binding or iPRA
endpoint follows. Lean axiom reports concern metatheory dependencies.

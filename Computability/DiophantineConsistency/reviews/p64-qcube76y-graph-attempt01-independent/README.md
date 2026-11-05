# Independent audit of the first 76Y graph-check attempt

The first low-priority guarded 76Y graph check did **not** pass. Its
[receipt](result.json) records process exit `−6` and no output object. The
[complete log](compile.log) contains a Lean exception reporting failure to
create a thread. The check ran with a 2 GiB address-space limit and Lean's
`-M2048` flag; the log does not establish the precise cause of the exception
or how far elaboration proceeded. Its 11,456 KiB recorded RSS is a sampled
value, not a guaranteed peak.

This read-only audit copied and rehashed the original receipt and log,
confirmed their hashes and internal `FAILED`/object-absence status, and
rechecked that all recorded direct input paths, hashes and companion absences
currently match the before/after guard records. It did not run Lean, prove
the graph, audit full transitive provider ancestry, or establish any
zero-existence or iPRA theorem.

| Artifact | SHA-256 |
| --- | --- |
| `result.json` | `1895e1acbf5077ab4159885c4fd6b49f4e89b92697e3c9ab00282e12f225e204` |
| `compile.log` | `32a60967270365f092cad81a408cf0e68f13aceab4359f32700f140a54129b9b` |
| Captured author runner `check_graph.py` | `eb4a65fd4071f4870c4674e0ae69244bd9a8313eea42e50dd994b1523d64d6d3` |

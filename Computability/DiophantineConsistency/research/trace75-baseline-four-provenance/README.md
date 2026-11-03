# Four selected BFS baseline producers

`check.py` is a reproducible **read-only, capture-relative** comparison of
the four retained baseline objects in the final trace75 fixed endpoint with
their recorded 127-stage producer run and the later BFS initial selection.
It invokes no Lean. Author attempt02 exited 0; checker SHA-256 is
`bc386cc00dbd55472b1e304792333fea7de6ee976db472144de4e03a0fa5f528`,
terminal SHA-256 is
`4a63b4c3cb7938ff3c6f49001f273a1a03d735d06c547a170bf8fd99c6c9540e`,
and complete output SHA-256 is
`72587a664b8d7a41704b146ad054c33bf1cdc70b9ae891fca18b11e9425a51b7`.
Attempt01 used the earlier checker before the reverse-reachability report was
added and is retained separately. An [independent audit](../../reviews/trace75-baseline-four-provenance-independent/README.md)
rechecked the producer evidence, selected direct bundles and 186-node impact
count; it did not independently replay Lean.

All four selected `.olean` files resolve to the actual regular outputs under
`/tmp/direct80-coherent-rebuild-2fbk3sj_/lib`, whose recorded producer
stages were 5, 9, 45 and 46. The historical producer result and its outer
wrapper record `PASS` and child exit 0. For each stage the checker verifies
that its retained copied source and corresponding current workspace source
have the recorded source hash; its producer output and selected BFS/final
companion hashes agree; the final selected path resolves to that producer
output; the recorded direct-before and direct-after bundles agree; each
direct bundle matches the final selected companion hashes; and the captured
serialized headers match the final headers and source imports. The full
realpaths, hashes and direct imports are in the captured output.

`ModelArithmetic` had an approved diagnostic exception: its recorded stdout,
after replacing the copied source path with `<SOURCE>`, exactly matches the
pinned warning baseline. The other three selected logs have no warning/error
diagnostic. The historical outer wrapper records its child exit as 0; this
packet does not itself establish an independently observed exit of that
wrapper process. The final assembly's actual outer tool exit was observed
separately in its own record.

This narrows the **direct producer-selection** boundary: the match is backed
by source, log and before/after direct-import records, not inferred solely
from coincidentally equal object bytes. It does not authenticate every
producer's upstream source-to-object history, all serialized transitive
selections, package-transitive or dynamic inputs, or establish an independent
Lean replay. It does not remove the final endpoint's inherited ancestry
qualification on its own.

For a prospective source replay of these four nodes, the captured final
endpoint header graph has 1,868 selected project modules. Reverse reachability
from the four nodes contains **186 modules including the four**; the full
sorted list is in attempt02's stdout. Individual reverse closures have 116
(`ModelArithmetic`), 115 (`ModelExponentialCongruence`), 182 (`PellOddFold`)
and 181 (`PellRecovery`) modules. These are capture-relative impact counts,
not an authenticated source-current build plan: a full current-source replay
would also need source snapshots and authenticated upstream inputs, could
discover changed imports or dynamic dependencies, and requires its own
fresh runner, review and validation.

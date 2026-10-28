# Actual DagPerm control table and root occurrence — author record

Author: `controller_certificate`. This is the author’s source review and bounded
fresh compilation, not an independent peer review. The final 251-line main and
54-line Checks are frozen. I read the complete proof code, Checks, unchanged
`PackedTables` prerequisite, and executed drivers before compilation. The large
literal was also decoded and compared in full by the preserved independent
path-successor and structured-occurrence reconstructions.

The new fixed table contains exactly 4,751 rows of the current `DagPerm` path.
Its root is node **0**, its node-count argument is **487**, and the complete
occurrence check uses fuel **488**. Every ordinary root exit restarts at positive
control 1; halt reaches absorbing zero. Neither table nor occurrence is a caller
premise.

`entryAt_eq` proves the generic indexed-tree traversal equals the actual
`leafEntries` lookup. Seventy-five kernel-checked blocks, each covering 64 possible
indices, prove every index below 4,751; the last block includes all remaining 15.
The quotient/remainder composition and both exact list lengths give the complete
catalogue equality. `packedRows_bound` separately proves there are no bits beyond
the last 36-bit slot. No sampled-row argument, `native_decide`, cap increase, or
omitted high slot is used. The packed literal is unchanged across all attempts:
171,033 bits / 42,759 hexadecimal digits, literal SHA256
`684a253753fd4e2e58a83b700747015dd405385d4ad5bf320596d4099821068d`;
canonical row-list SHA256
`42bcd1c057e73b82f6e13d151dbe280f1d30e06784575e788dbe2a8430704dcd`.

The final public arithmetic interface supplies the genuine represented internal
run, instruction specification, zero/one/addition/absorbing-zero laws, and normal
and halt adapters from explicit structured `IRun` hypotheses. The finite
whole-root `root_occB` and `root_occ` themselves are unconditional. This does not
yet establish a structured interpreter run, the actual EnumStep dispatch,
equivalence to p215, positive simulation clocks, source-ZFC calibration, or an HA
endpoint. Those boundaries remain open.

## Fresh compilation and provenance

The selected prerequisite closure has 138 custom modules including 95 Foundation
modules: 137 reused modules / 422 recorded artifacts, 39 external boundary
modules, and one explicitly refreshed unchanged prerequisite, `PackedTables`.
No Foundation or broad closure was rebuilt. Seven source-identical DagLoops
objects use the independent peer provider
`/tmp/arithmetic-dag-loops-peer-v9mmg0s_/lib`; its later root acceptance at
`b5459f3024` is recorded separately without rewriting the earlier pending-status
plan or attempt inputs.

All compiler calls used the pinned Lean 4.32.0 executable, `-M6000 -j1
-DElab.async=false`, one Lean thread, a private explicit dependency overlay, and
a 512 MiB free-space guard. No project shared cache was included in `LEAN_PATH`.
Fresh outputs are regular, nonsymlink files. Sources and executed drivers were
snapshotted and pinned; prerequisite and final source/object pins were rechecked.
The final attempt recorded 1,219 pin observations. The durable freeze rechecked
6,076 observations across all five attempts; these are repeated observations,
not a count of distinct dependencies or a full fresh closure claim.

Successful records:

| Module | Seconds | Source SHA256 | Object SHA256 |
|---|---:|---|---|
| `PackedTables` (unchanged fresh prerequisite, attempt 1) | 1.732 | `a09289dadc997e0bb58ff6f111d22044b6a8fdff6becda8c9e378e0ed1ea4be9` | `13439cd20dd48e2e82ea007bb9927451680d765a6b269e17746ed7bbe55714f0` |
| `ArithmeticDagControlPerm222` (attempt 5) | 468.447 | `1851444d564e63c2296c2e64335d95008465da9c1fd837bef399886f691e7fb4` | `93b2126d0ab5d85e27740293b15807d52c4c15675b751b3b6410848af12025d9` |
| `ArithmeticDagControlPerm222Checks` (attempt 5) | 1.816 | `8bd6ed4c2ad967d2cee849082463ce95324383f8fb662f3564c895fc4df0b772` | `b6a16c3ce17b0116c5e97ce70bd6a3a0209ba249439cc2f3bc587bca1267a522` |

The final main log is empty, with maximum RSS 2,914,012 KiB. Checks printed twelve
axiom reports, all contained in `propext`, `Classical.choice`, and `Quot.sound`.
The packed bound uses only `propext`; the complete occurrence check and its
soundness corollary use `propext` and `Quot.sound`. The first actual table
instruction is also exercised over arbitrary internal models, without an
occurrence hypothesis.

## Preserved development history

All five full attempts remain in the evidence manifest, with original commands,
source snapshots, logs, timings, and successful objects.

1. Monolithic catalogue list equality naturally terminated with stack overflow
   after 124.603 seconds; the unchanged `PackedTables` refresh had already passed.
2. The first complete list-slice block proof exited normally with elaboration
   errors after 224.702 seconds (opaque decision predicate, dependent empty-Fin
   branch, and small unfolding/cast simplifications).
3. The corrected list-slice block proof naturally terminated with stack overflow
   after 1,247.762 seconds. Its healthy single process was retained throughout;
   it was not interrupted or restarted because of elapsed time.
4. The indexed-tree revision exited normally after 472.202 seconds with two
   generic helper errors: optional-list-index syntax and the packed lookup
   conditional simplification. The fixes were local generic identities.
5. The final indexed proof and Checks both passed, with the full original table
   and root-occurrence endpoints retained.

Three separately preserved generic-prefix diagnostics include one rejected
outside-root source invocation and two successful narrow helper checks. They
were not imported into the final module and do not count as whole endpoint
builds. The final proof adds the explicit high-bit bound. There is no failed
attempt omitted from this record.

Durable packet:
`reviews/arithmetic-dag-controlperm222-replay.json`, SHA256
`979d525f3e40b6d7037b3ee3b8ad210fbfc64410ed5183c7fcedc02f6d22cc4b`.
The 66-file evidence manifest is
`reviews/arithmetic-dag-controlperm222-author-replay/FILES.json`, SHA256
`1889feb1bcfad0035b58fe8277ac9c794e6037473a791ee1465c90310860f80b`.
The final private provider is
`/tmp/dag-controlperm222-controller-author-_s3qdbgq/lib`.

The complete replay packet is staged work for root and independent review. No
Git action, accepted-source edit, shared-object replacement, or proof-endpoint
promotion was performed by this author.

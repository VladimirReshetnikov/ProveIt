# Phase17 Lean evidence

The [terminal proof result](result.json), [owner evidence audit](result-review.json)
and [independent readback](../integration/resumed-peer/README.md) pass for the exact
combined selection: 199 project modules and fourteen typed clients. There are
171 freshly checked providers and 42 source-transitive phase16 reuses, plus two
fresh endpoint audits. The endpoint closure contains 174 modules and 1,749,188
source bytes. All nine site batches were checked fresh, covering 105 blocks,
4,751 decoder leaves and 6,176 outcomes. The selected machine remains 215 states.

The ten endpoint audit reports, seventy earlier API reports, ten compatibility
reports and five WFTheory reports retain their exact expected assumptions.
The two new direct-seed theorem reports and three new client reports each use
exactly `propext`, `Classical.choice` and `Quot.sound`. All fourteen clients and
both endpoint audits have zero warnings. Project records contain eighteen warning
occurrences: seventeen fresh and one reused. Every fresh warning headline already
appeared in the same module's earlier accepted log.

One internal report was explicitly reviewed: `source_tree_eq` changes from no
axioms to `propext` because its type now names a computed tree through the existing
`ptree`/`toTree` definition. Its source and `by rfl` proof are unchanged. The literal
program nodes and independent `sourceTree` remain axiom-free. The original compiler
invocation passed but its exact-profile policy failed; the guarded metadata
transition preserves all 177 completed providers and rechecks that module. There
are 172 provider compiler invocations for 171 accepted fresh providers, with two
audits and a separate diagnostic invocation in addition. Every other retained
profile still has an exact-match gate. The independent
[mathematical review](../integration/profile-peer/review.json) and raw failure,
diagnostic and transition bytes are preserved in the packet.

The first metadata-audit invocation failed on a variable-name collision after
reading the proof evidence. Its source, stderr and outer exit-one record are
retained. The corrected [audit helper](review_actual.py) passes; it changes only
the two identifiers on the colliding census line. Neither issue required a
production proof change or a complete Lean rerun.

The [archive](evidence.tar.gz), [alias index](index.json) and [capture receipt](capture.json)
contain 579 distinct byte blobs, 905 logical entries and 891 source aliases.
The 743-file raw subset includes all selected sources, fresh invocation sources,
logs and records, both audits and metadata. Additional pinned context preserves
source reviews, ten cleanup-before snapshots and both failed invocations.
Sixteen named phase15/phase16 evidence files remain hashed external boundaries;
their archive bytes are not duplicated. No compiled objects are shipped.
Archive SHA-256: `5aa2c1f9a0ca891cb1427400c43d4a638ac3ad78f7abdd5a193e4b009e50270d`.

Logical paths in `index.json` identify their `blobs/<sha256>` members. Every created
member was read back and hashed; [independent capture review](capture-peer/README.md)
also checks the final archive and index. Captured historical statuses remain
unchanged. The packet is data: no captured helper, generator or archive reader is
executed. [Unpacked clients](clients/) and [audits](audits/) are provided for reading.

The selected [check plan](check-plan.json), [historical runner](check.py),
[capture helper](capture.py) and [capture map](capture-config.json) retain their
original absolute-path evidence bindings. For a fresh endpoint reproduction from
current repository source, use the [portable Lean driver](../../../lean/README.md)
in a new output directory. It rebuilds the current endpoint closure and its two
audits. The fourteen extra typed clients and compatibility/macro roots are the
additional scope of this archived checkpoint, not a claim about every 217–225
certificate stack. No internal PA formalization or minimal-state theorem is
established here.

# Independent AQ22 historical paired-artifact audit

The independent point-in-time audit passed with actual session 13719 exit 0;
the separate all-parent and sibling inode-isolation check also exited 0.
[terminal-observation.json](terminal-observation.json) records those exits,
and the [main receipt](receipt.json) and [inode receipt](hardlink-receipt.json)
pin their evidence.

The review rehashed all 1,247 frozen source rows and checked every one of the
37 added Git source blobs. For each sibling it bound all 1,210 seed hashes to
that sibling's pinned parent-state output inventory and rehashed both the
parent and copied artifacts. It checked the 37 fresh output objects, logs,
102 direct-import occurrences, all recorded input/output companion guards,
exactly 94 ordered per-module diagnostic names, and complete output inventory.
It compared the siblings' source, object, log, direct-import and report
records. A separate check rejects links to **any** parent output inode, as
well as links between or within sibling inventories; synthetic hardlink and
changed-seed controls were rejected.

The audit binds the actual observed coordinator and outer launcher exits,
stable preparation HEAD, historical parent pair and its independently
verified receipt, pinned toolchain and provider, and all 1,540 Foundation
artifacts. It checks the standard endpoint's positive-shift AQ22 literal and
selected embedded Gödel–Gentzen-translated Foundation consistency sentence.
The snapshot records 15 workspace-source drifts and is historical.

The supplemental [state-link check](state-link-check.py) also binds each
sibling's old/new snapshot, parent-pair and driver hashes directly to its
preparation and coordinator records. Its [receipt](state-link-receipt.json)
and [observed exit](state-link-observation.json) are separate. The two
builders recorded different workspace HEADs after preparation; the result
remains tied to the frozen historical sources and pinned additions.

An [earlier attempt](attempt-1-observation.json) was deliberately stopped
with exit 143 after the reviewer noticed that seed hashes also needed an
explicit binding to the parent-state output records. Its exact
[incomplete script](attempt-1-script.py) is retained only as history and must
not be used as passing evidence; the successful script adds that binding and
a mutation control.

This is an independent artifact audit of two historical rebuilds, not another
Lean replay, a theorem interpreting a PDF, or an identification of the
translated sentence with an arbitrary unmodified Con(ZFC) formula. Input and
companion guards are point-in-time observations; package-transitive and dynamic
loads and between-observation mutations remain inherited. The Foundation
provider's outer wrapper exit was not observed. See the receipt for exact
counts, hashes and time spent.

Rerun with the pinned temporary artifacts available, after preserving and
moving aside only this packet's two receipts:

```sh
ionice -c 3 nice -n 19 python3 Computability/DiophantineConsistency/reviews/ipra-aq22-historical-pair-independent-audit/audit.py
python3 Computability/DiophantineConsistency/reviews/ipra-aq22-historical-pair-independent-audit/hardlink-check.py
```

The main audit rate-limits hashing to 8 MiB/s. Both checks refuse to overwrite
receipts and reject optimized Python.

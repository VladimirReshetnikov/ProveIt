# Independent AQ17 historical paired-artifact audit

The independent point-in-time audit passed with actual session 70886 exit 0.
The separate all-parent/sibling inode check and build-state link check also
exited 0. [terminal-observation.json](terminal-observation.json) records the
actual exits; the [main receipt](receipt.json), [inode receipt](hardlink-receipt.json)
and [state-link receipt](state-link-receipt.json) pin their evidence. The
freezer and preparer process observations are copied from the completed run.

The review rehashed all 1,254 frozen source rows and checked every one of the
44 added Git source blobs. For each sibling it bound all 1,210 seed hashes to
that sibling's pinned parent-state output inventory and rehashed both parent
and copied artifacts. It checked 44 fresh outputs and preserved logs, 123
direct-import occurrences, all input/output companion guards, exactly 109
ordered per-module diagnostic occurrences and the complete output inventory.
It compared sibling source, object, log, direct-import and report records. A
separate inode check rejects links to any parent output or to another sibling
output; synthetic hardlink and changed-seed controls were rejected.

The review binds the actual observed launcher and coordinator exits, stable
preparation HEAD, independently audited historical parent pair, pinned
toolchain/provider and all 1,540 Foundation artifacts. It checks the standard
AQ17 endpoint's positive-shift literal and selected embedded Gödel–Gentzen
translated Foundation consistency sentence. The snapshot records 15
workspace-source drifts and is historical.

This is an independent audit of two historical builds, not another Lean replay,
a theorem interpreting the PDF, or an identification of the translated
sentence with an arbitrary unmodified Con(ZFC) formula. The display's fixed
decoder, table, rank and port recipe remain manually transcribed in finite
checks. Package-transitive and dynamic loads and between-observation mutations
remain inherited; the Foundation provider's outer wrapper exit was not observed.

With the pinned temporary artifacts available, preserve and move aside this
packet's three receipts before rerunning:

```sh
ionice -c 3 nice -n 19 python3 Computability/DiophantineConsistency/reviews/ipra-aq17-historical-pair-independent-audit/audit.py
python3 Computability/DiophantineConsistency/reviews/ipra-aq17-historical-pair-independent-audit/hardlink-check.py
python3 Computability/DiophantineConsistency/reviews/ipra-aq17-historical-pair-independent-audit/state-link-check.py
```

The main audit rate-limits hashing to 8 MiB/s. All checks refuse to overwrite
receipts and reject optimized Python.

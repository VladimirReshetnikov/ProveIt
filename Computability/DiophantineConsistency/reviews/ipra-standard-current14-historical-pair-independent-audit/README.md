# Independent audit of the historical original-14 pair

The independent paired-artifact audit passed with actual session 27623 exit 0.
The separate all-parent/sibling inode check and build-state link check also
exited 0. [terminal-observation.json](terminal-observation.json) records the
actual exits; the [main receipt](receipt.json), [inode receipt](hardlink-receipt.json)
and [state-link receipt](state-link-receipt.json) pin their evidence.

The review rehashed all 1,226 frozen source rows and checked every one of the
16 added Git source blobs. For each sibling it bound all 1,210 seed hashes to
that sibling's pinned parent-state output inventory and rehashed both the
parent and copied artifacts. It checked the 16 fresh outputs and preserved
logs, 51 direct-import occurrences, all input/output companion guards, the
four exact diagnostic reports and complete output inventory. It compared the
siblings' source, object, log, direct-import and report records, and checked
that no output links to any parent or sibling output inode. Changed-seed and
synthetic hardlink controls were rejected.

The review binds the actual observed launcher and coordinator exits, stable
preparation HEAD, historical parent pair and independently audited receipt,
pinned toolchain/provider, and all 1,540 Foundation artifacts. It checks both
standard-theory endpoint statements: the one relating `noZero14` to the
selected mapped refutation negation, and the one relating it to the selected
embedded Gödel–Gentzen-translated Foundation consistency sentence. The
historical `noZero14` source uses the two split sides of the positively shifted
14-variable expression. The separate sibling state-link check records the
later workspace HEAD seen by each builder; the result is still tied to the
frozen historical snapshot and pinned additions. The snapshot records 15
workspace-source drifts.

This is an independent audit of two historical Lean builds, not another Lean
replay or a formal theorem interpreting `equation.pdf`. The separate
[finite historical PDF binding review](../equation14-historical-literal-binding-independent/README.md)
retains the manually transcribed decoder, table, rank and port-recipe boundary.
Nor does the audit identify the translated sentence with an arbitrary
unmodified Con(ZFC) formula. Package-transitive and dynamic loads and
between-observation mutations remain inherited; the Foundation provider's
outer wrapper exit was not observed.

With the pinned temporary artifacts available, preserve and move aside this
packet's three receipts before rerunning:

```sh
ionice -c 3 nice -n 19 python3 Computability/DiophantineConsistency/reviews/ipra-standard-current14-historical-pair-independent-audit/audit.py
python3 Computability/DiophantineConsistency/reviews/ipra-standard-current14-historical-pair-independent-audit/hardlink-check.py
python3 Computability/DiophantineConsistency/reviews/ipra-standard-current14-historical-pair-independent-audit/state-link-check.py
```

The main audit rate-limits hashing to 8 MiB/s. All checks refuse to overwrite
receipts and reject optimized Python.

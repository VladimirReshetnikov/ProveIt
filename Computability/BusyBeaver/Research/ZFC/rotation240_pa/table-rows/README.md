# Exact packed-table equality for Rotation240

[`TableRowsRotation240.table_eq`](../../../../Lean/BusyBeaver/ZFC/TableRowsRotation240.lean)
proves that the complete packed interpreter table equals the catalogue of the
exact Rotation240 decoder tree. All 6,455 entries agree in opcode, physical
register and both stored successor fields, including the second successor on
non-test instructions. The equality also fixes the table length, excluding
unexamined extra entries.

The construction combines the [counted-tree identity](../counted-tree/README.md)
and [generic binding theorem](../table-binding/README.md) with fresh checks at
every leaf. The existing binary-site coverage supplies a partition into 530
cuts. Its proofs are not reused as packed-row proofs. There are 529 fresh cut
checks and one alias of the separately [checked twenty-leaf pilot](../table-rows-pilot/README.md),
followed by 529 structural joins and the two final theorems. Every cut retains
its complete source path; every join requires both children.

All 35 generated modules pass source compilation and separate audits: 1,061
axiom probes and 1,061 typed callers, zero warnings, and only standard Lean
axioms. Including the pilot gives 1,062 probes and callers. Checks ran serially
under default proof limits, each source/audit pair sharing 120 seconds with
one thread and 4,096 MiB. The 46 base project prerequisites and previously
passed generated modules supply exact source/object pairs; the final module
uses 81 project prerequisites. Three external cache boundaries and Init/Omega
are recorded without rebuilding or claiming whole-cache attestation.
Total source/audit compiler time was 288.632 seconds; the slowest pair took
11.278 seconds. Both final theorems report only `propext` and `Quot.sound`.

The [batch record](batch.json), [publication summary](../../results/w6-table-rows240-publication.json)
and [final raw verification](../../results/w6-table-rows240-final-verification.json)
identify the accepted executions. The [generation manifest](manifest.json)
lists all cuts, joins, dependencies and source/audit hashes. The
[history](history.json.gz) preserves exact source/audit snapshots, raw logs,
preparation records, guards, reviews and any unsuccessful attempts. It is a
gzip-compressed JSON mapping of relative archive names to base64 file bytes.
Recorded scratch paths describe the original executions; the public Lean
sources and [audits](audits/) are also unpacked in this repository.
Audit files retain their checked bytes, including their trailing blank lines.
The [completed-run review](completed-run-review.json) confirms the raw records,
provider identities and captures, and explicitly discloses runner authorship.

This closes the finite table-identification obligation of W6. It does not
prove the unbounded binary/interpreter simulation in arbitrary arithmetic
models. That transport, followed by sentence evaluation and completeness,
is still required for the PA statement about the exact binary machine.
The new table proof retains the underlying construction's attribution to
Mira-Cult, Jeff Ketchersid, Andrew James Wade and the maintained ProveIt work.

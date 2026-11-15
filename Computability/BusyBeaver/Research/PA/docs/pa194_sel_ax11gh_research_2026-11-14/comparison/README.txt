Comparison data and exact scope
===============================

all_194_designs.csv/json: every one of the 110 spanning 194-control classes,
with names, evidence category, mechanism, canonical identities and source.
packet_ledger87.csv/json: 82 filed packets plus the five current incoming
deliveries. Reused names are retained at this delivery level.

frontier194/: one complete literal representative for each graph class.
frontier194.json: exact byte hashes, tuple hashes, source occurrences and
ordinary quotient sizes. census.py verify rechecks the whole frozen corpus
without requiring the repository or incoming archives.

census.json and census_summary.json: the 1,569 literal .tm occurrences,
802 distinct contents, all sizes, including excluded fragments. The field
named invalid_tables means outside this complete-two-row/one-terminal
recognizer. It does not establish that a fragment is an invalid program.
Seven 194-control fixtures lack a spanning root and are recorded separately.

All 695 tracked PA .tm files were obtained. source_integrity.json checks
those files and the five current ZIPs against their exact Git blob IDs.
The source revision is 603c58ca3bd6bf3222fcfc4e308e6b079f65d573.

The complete BFS transition tuples, minimized over all spanning roots,
establish graph equality. Strong comparison additionally permits global
bit exchange, left/right reflection, and ignores terminal write/move.
It is intentionally stronger than the blank-preserving equivalences:
global bit exchange need not preserve an all-zero initial tape.
No graph novelty test by itself establishes arithmetic correctness.

Reported principal constructions, supplements, research seeds/auxiliaries
and rejected proposals remain separate categories. Mechanism annotations
from the incoming AX11G ledger are explicitly attributed; the sixteen
additional current classes are reconciled to exact tables. The archive
does not assert that every historical calibration suite has been rerun.

scan_json.py reads all 668 JSON files in the five current incoming archives
with the retained explicit-table recognizer. It adds no frontier class.
The scope does not include evaluating arbitrary generators or inferring
an unevaluated transition table from prose.

Offline comparison of the two new machines, from the archive root:
  python3 comparison/census.py verify machines/SEL/machine/pa194sel.tm machines/AX11GH/machine/machine.tm

Full recollection (requires the pinned external source inputs):
  python3 comparison/census.py build /path/to/ProveIt /path/to/extracted_incoming
  python3 comparison/assemble_ledgers.py /path/to/ProveIt /path/to/extracted_incoming

The release verifier also asserts that both candidates are distinct from
each other, since that is a separate condition from novelty to the corpus.

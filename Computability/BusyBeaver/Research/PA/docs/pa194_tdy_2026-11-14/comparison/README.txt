FROZEN PA MACHINE COMPARISON
============================
Repository: VladimirReshetnikov/ProveIt
Snapshot: 4be5c6e3a10292a7466f5d3687e3b39615ff049b

RESULT
------
PA194TDY has no exact graph match in the frozen comparison, allowing arbitrary
control renaming/root, left/right reflection, global bit exchange, and ignoring
the final halt transition's write/move. The replay also searches candidate-sized
reachable components of larger tables. These finite checks establish relative
structural novelty. They do not prove the consistency calibration or a global
priority claim.

Run from the release root, Python 3.10+ and standard library only:

    python3 comparison/verify_novelty.py

The recorded result is novelty_receipt.json. It checked 780 byte forms and
29,294 reachable components of size 194. Comparison uses complete serialized
transition tuples, not merely matching or unequal hash values. No network,
external checkout, compiler, or proof assistant is required for this replay.

CONTENTS
--------
corpus_tables.json       Exact frozen table bytes and source locators.
literal_tables.json      Byte-form inventory, starts, terminal counts, paths.
literal_classes.json     Full graph groups and all associated locators.
literal_classes.csv      Compact machine-readable full-class inventory.
frontier194.csv/json     All 82 spanning 194 classes plus two disconnected
                         diagnostic byte forms, with attributed evidence labels.
packet_ledger.csv/json   All 61 filed deliveries and all 11 incoming ZIPs.
archives.json            SHA-256, byte size, member count and outer references
                         for 25 distinct recursively examined ZIP archives.
census_summary.json     Scope, counts, restrictions and state distribution.
evidence_summary.json   Attributed 194-state evidence-category counts.
source_census/          Original repository ledger/table inputs and prior
                         comparison metadata used for evidence attribution.
comparison_manifest.json Core comparison file hashes.

SCOPE
-----
The literal corpus includes every one of the 535 official filed representatives,
all 14 direct PA .tm files outside the filed-documents tree, all 11 incoming
ZIPs, and all six retained historical ZIPs, recursively expanded. Identical
nested ZIP bytes are scanned once. The broad numeric-table parser accepts
complete five-column binary rows in .tm/.txt/.tsv/.csv files, including research
controls and rejected machines.

The fresh supplementary JSON scan decoded the 21 repository files identified
by the inherited QN JSON census, plus JSON files inside every incoming and
retained historical archive. It examined 1,894 JSON files and materialized 85
complete table occurrences. This is not a fresh scan of all repository JSON
files. The inherited larger scan and its explicit occurrence list are retained
in source_census/inherited_json_census.json. Arbitrary code-only generators are
not executed by the census and are not certified by a table count.

There are 3,442 recognized occurrences, 780 byte forms, 642 full spanning graph
classes and 10 disconnected byte forms. The main 194-state frontier has 82
spanning classes: 40 principal/supported packet constructions, 7 supplementary
constructions, 25 auxiliaries, 4 research seeds, 6 rejected. These labels are
historical attributions, not fresh proofs of every listed machine. All 82 have
one external halt. Across all 780 forms, 772 have one external terminal label;
8 small or disconnected diagnostics have zero or multiple exits. Missing-row
targets are treated as terminal exits in the broad diagnostic comparison.
Disconnected tables are never equated solely by a maximum reachable component.

REBUILDING THE FINITE INVENTORY
------------------------------
To reclassify the frozen bytes without modifying the release:

    python3 comparison/inventory.py --corpus comparison/corpus_tables.json \
      --candidate artifacts/pa194_tdy.tm --output /tmp/pa194_census_replay

The archive-reference ledger is provenance from the original extraction, so a
frozen-table replay will not recreate archive membership counts. Literal class
and byte counts are reproducible from the supplied corpus. The JSON decoder is
adapted, with source attribution, from the supplied QN packet's scanner. The
exact novelty comparator and corpus assembly are independently provided here.

The report appendix is report/comparison_summary.tex. Its generator is
comparison/generate_comparison_report.py and uses frozen inputs. Original
packet descriptions and evidence labels retain source attribution; mathematical
correctness claims remain those described in the report's proof-status section.

COMPARISON DATA AND REPRODUCTION
===============================

Pinned ProveIt commit:
  d8d4fb10149d6a76a56e615a35648c8c32847cf4

Run the commands below from this comparison/ directory. Python 3.9 or later
and its standard library suffice except that the independent 193-state
screen also needs a C++17 compiler (g++ by default). Full source recensus
requires an external checkout of the pinned repository; offline novelty
and the 193-state screen use only the data bundled here. No proof assistant
is needed for these finite/structural checks. Run Python without -O or -OO:
the checkers use assertions as verification failures.

1. What is counted
------------------

The source scope is all 760 tracked .tm files anywhere under
Computability/BusyBeaver/Research/PA, together with .tm members recursively
inside the seven docs/incoming ZIPs. Nested references are included each
time they occur. The resulting census has 5,506 table occurrences, 1,347
distinct byte payloads, and 1,154 whole-transition-graph classes.

The 194-state corpus has 530 classes: 528 graphs with a spanning root and
two disconnected diagnostics. The 193-state corpus has 55 spanning graphs.
Spanning means that some control can reach all working controls in the
directed transition graph; it is not a claim about the blank trajectory.

These counts identify working states up to renaming and disregard choice
of root. They PRESERVE read/write symbols, move directions and halt-entry
actions. They are not counts modulo reflection, global symbol exchange or
erased halt actions. Those stronger identifications are used separately
by the exact novelty checker described below.

The inherited all-roots classifier is complete for spanning graphs but
retains only a largest reachable component for a nonspanning graph. We
checked all 23 nonspanning inherited-key groups with exact full-table
isomorphism. One group splits into two distinct 194-state diagnostics.
Thus summary.json's legacy 1,153/529 key counts differ from the corrected
1,154/530 counts in strict_summary.json and final_summary.json.

The semantic roster contains 91 named graph classes in 32 mechanism
families, extending the attributed 83-design roster in the incoming
marker-separation packet. It covers the supplied constructions, explicit
outputs and named designs. It does not enumerate all programs that an
arbitrary generator could produce. These are structural and historical
classifications, not 91 or 530 established consistency theorems.

2. Offline exact structural novelty
-----------------------------------

  python3 novelty.py ../machines/PA194H5X_MF/machine.tm --out /tmp/h5x-novelty.json
  python3 novelty.py ../machines/PA194JH5X_MF/machine.tm --out /tmp/jh5x-novelty.json

The default corpus is current_194_representatives/ beside the script.
It contains all 530 representatives plus the provenance index
current_194_representatives/index.json. An alternative directory
can be supplied with --corpus PATH.

The matcher permits arbitrary working-state renaming/root choice, global
left/right reflection, global bit exchange, and erased terminal-entry
write/move actions. Bit exchange is a stronger structural comparison;
it does not preserve the fixed all-zero blank specification. Refinement
only prunes the search; full backtracking and edge verification establish
isomorphism. novelty_current530.json and pairwise_novelty.json retain the
two new machines' results. novelty_positive_control.json records one
exact match for the previously supplied AX11GDH table.

3. Offline independent 193-state replay
--------------------------------------

  python3 audit193.py --output /tmp/pa193-new-replay

Keep audit193.py, audit193.cpp and audit193/ together. The input directory
contains index.json and 55 hashed tables. --input PATH changes this data
directory; --compiler PATH changes the compiler executable. Without
--output the script creates a new temporary output directory.

The wrapper verifies every input hash, compiles its independent scalar
simulator, and tests every control of every table as a possible blank
start. The expected 10,615 outcomes are:
  112 HALT; 10,499 RAY; 4 LIMIT at 100,000 transitions.

RAY is a finite-prefix certificate: read zero, the zero-read transition
returns to the same control, and the half-line ahead has no one-cells.
The same transition then repeats forever, even if it writes ones behind
the moving head. LIMIT is unresolved by this screen. No lower bound for
arbitrary PA-consistency machines follows. The four capped trajectories'
source mechanisms have separate semantic or compilation failures.

4. Full source recensus
----------------------

Obtain the pinned ProveIt checkout with the COMPLETE PA tree and all seven
incoming ZIPs. A sparse checkout limited to PA/docs omits 14 .tm files and
97 JSON files. All required source files are listed in the binding JSONs;
unrelated files in a checkout are ignored. The census verifies every
required file's SHA-256 before using it. If .git exists, HEAD must equal
the pinned commit.

  python3 inventory.py /path/to/ProveIt --out /tmp/pa-census
  python3 finalize_census.py /path/to/ProveIt --census /tmp/pa-census \
      --representatives /tmp/pa194-representatives

Dependencies in this directory:
  inventory.py: machine_classes.py, MACHINES.tsv, source_blob_binding.json
  finalize_census.py: novelty.py and the census produced above

Read strict_summary.json or final_summary.json for corrected counts.
classes.json and summary.json retain the inherited-key grouping for
comparison with the historical catalog. whole_graph_classes.json is the
corrected graph partition; disconnected_audit.json records every split.

The optional inventory.py --reuse PATH can reuse SHA-256-keyed
classifications from a prior files.json. Omit it for a fresh classification.
The optional --overlay PATH exists only to accommodate a partial checkout;
our historical run used exact Git-verified missing files in such an overlay.
No overlay is needed for a complete checkout. Full reproduction should use
the complete pinned source tree, not rely on that scratch-directory history.

5. Explicit JSON supplement
---------------------------

  python3 json_supplement.py /path/to/ProveIt \
      --tm-census /tmp/pa-census/files.json --output /tmp/pa-json-supplement

Dependencies: schema_parser.py, machine_classes.py, source_blob_binding.json,
source_json_blob_binding.json and the .tm census from step 4. The supplement
verifies all 11,258 tracked PA JSON blobs and the incoming archive blobs.
It reads nested duplicate ZIP payloads once. The optional --overlay PATH
serves the same historical partial-checkout purpose as above.

The completed scan inspected 12,520 JSON payload occurrences (8,942 unique
bytes) in PA and nine distinct ZIP payloads, recognized 365 complete
193/194-table occurrences in 198 normalized forms, and found no additional
whole graph. Its 136 inherited graph keys include the same disconnected
diagnostic collision. The two nonspanning normalized tables are byte-for-
byte copies of the two already counted .tm diagnostics; this is recorded
in nonspanning_audit.json, not inferred from their colliding keys.

The recognizer supports numeric five-column matrices, action-pair arrays,
flat action arrays, record arrays, keyed rows and embedded text. It only
records complete 193- and 194-control tables. It does not execute arbitrary
generators or extract tables represented only in Lean definitions or
printed TeX. summary.json gives the scope; payloads.json records every
examined JSON payload; occurrences.json records recognized table locations;
identities.json binds the 198 normalized tables included in the directory.

6. Independent incoming initialization replay
--------------------------------------------

  python3 check_incoming.py /path/to/ProveIt --output /tmp/pa194-startup

This requires the seven exact pinned ZIPs in docs/incoming and the bundled
incoming_principal_audit.json/source_blob_binding.json. It reads their
17 principal/companion tables directly from the archives, verifies their
hashes and shapes, and uses its own literal set-of-one-cells simulator.
Each machine reaches the same complete seed tape, native control 84 and
head -2 at its claimed finite initialization time. The checker needs no
separate extraction tree. With no --output it uses a new temporary folder.
This establishes initialization only, not nonhalting or Con(PA) calibration.

7. Ledgers, provenance and attribution
-------------------------------------

  current_census/files.json       all 5,506 .tm occurrences and classifications
  current_census/whole_graph_classes.json   corrected 1,154 graph classes
  current_194_representatives/    all 530 comparison tables and provenance index
  named_designs91.csv/.json       semantic names, aliases and exact table bindings
  families32.csv/.json            mechanism families and source distinctions
  family_table32.tex              typeset family comparison
  packet_ledger100.csv/.json      93 filed packets plus seven incoming deliveries
  incoming_principal_audit.*      independent finite initialization receipts
  source_blob_binding.json        760 .tm files and seven ZIPs, exact Git/SHA-256
  source_json_blob_binding.json   all 11,258 tracked PA JSON blobs, Git/SHA-256
  json_supplement/                JSON records, normalized tables and receipts
  audit193/                      55 tables, 10,615 outcomes and exact input hashes
  comparison_narrative.txt        explanatory comparison and proof-status notes
  report_fragments.tex            TeX version of that narrative

machine_classes.py and MACHINES.tsv are attributed snapshots from pinned
Computability/BusyBeaver/Research/PA/docs. The historical classifier's
disconnected-graph limitation is corrected by finalize_census.py; do not
use the inherited script alone to infer full-graph equality in that case.

schema_parser.py is copied from:
  docs/incoming/pa194_marker_separation_2026-11-14.zip
  !pa194_marker_separation_2026-11-14/comparison/audit_corpus.py
Only its documented parsing functions are imported. The semantic ledger
extends that packet's attributed 83-design/29-family account. The current
recensus, exact matcher, disconnected audit and independent startup/193
screens are the additional work supplied here.

The later manuscripts' written iPRA calibration, the new relative machine
theorem, and the unfinished machine-specific kernel formalization are
separate proof statuses. Hashes, graph comparisons and finite replays do
not establish an absolute consistency theorem by themselves.

AUDIT AND NOVELTY ARTIFACTS
Repository: VladimirReshetnikov/ProveIt
Pinned commit: 4be5c6e3a10292a7466f5d3687e3b39615ff049b

Main results
------------
packet_ledger72.csv / .json: all 61 filed and 11 incoming deliveries,
with overview summaries, pinned URLs and overview-file SHA-256 values.
comparative_findings.txt: detailed comparison and limitations.
current_census/summary.json: exact structural totals and recognition scope.
current_census/census.json: per-table identities, occurrences, Git-blob
provenance and nested-archive records.
current_census/frontier_tables/: every recognized spanning 193-196 graph
representative; numeric binary L/R five-column format.
all_machine_classes.csv: all 638 recognized spanning one-halt classes.
frontier194_current.csv / .json: all 82 current 194 classes, with source
locators, mechanisms and historical evidence labels.
frontier193_current.csv / .json: all 53 current 193 classes, with exact
provenance and rejection/verification scope.
rejections193_summary.json: fresh independent rejection replay summary.
rejections193/: complete per-start certificates for the 52 physical
193-state classes; the separate coefficient-three logical rejection is
explicitly attributed rather than freshly replayed.
ax11q6_novelty.json: exact structural comparison of the new candidate with
all 82 prior 194-state classes, allowing all listed cosmetic transformations.
appendix_deliveries.tex: report-ready linked LaTeX ledger of all 72 deliveries.
appendix_frontier194.tex: report-ready linked LaTeX ledger of all 82 historical
194-state classes. The evidence labels attribute the original packets.
candidate.tm: exact PA194AX11Q6 table used for the independent novelty audit.
replay_audit.py and offline_replay_receipt.json: combined fresh offline replay.

One-command offline audit
-------------------------
    python3 replay_audit.py --receipt /tmp/audit-replay.json

This script uses only the Python standard library and the bundled CSV, JSON
and table files. Its parser, literal simulator and canonicalization routine
are self-contained. It replays all 10,036 blank starts and compares their
complete outcomes with the retained per-start records. It recomputes all 53
193-state and all 82 194-state canonical tuples and tests the candidate's
exact full tuple against every historical class under the broad cosmetic
equivalences. Digest checks bind provenance; tuple equality decides novelty.
The coefficient-three logical rejection is the one explicitly excluded
logical-proof replay, not an unreported bounded simulation.

The default candidate is the exact included candidate.tm. To bind the audit
directly to the enclosing package's delivered machine, use:
    python3 replay_audit.py --candidate /path/to/delivered/machine.tm \
      --receipt /tmp/audit-replay.json
The script requires the exact recorded candidate digest and complete 194-state
blank-start specification. Do not use Python -O, which disables assertions.

LaTeX appendix integration
-------------------------
After the report's appendix command, input appendix_deliveries.tex and
appendix_frontier194.tex. Both define their own section headings and scope
notes. They require booktabs, longtable, array, hyperref and xurl. Formatting
changes are enclosed in local groups. Sources are clickable short labels;
the full paths and source lists remain in the CSV/JSON ledgers.
Regenerate both appendices from those ledgers with:
    python3 generate_appendices.py

Reproduce the fresh short certificates offline
---------------------------------------------
From the directory containing this file:
    python3 classify_193.py

This requires only Python 3 and the included current_census files,
scanner/literal_inventory.py, and variant193_manifest.json. It replays
every working control as the initial state of an entirely zero tape for
each of the 52 physical 193-state classes. It writes per-class JSON receipts
and the CSV ledger. The current result is 10,036 cases, 106 halts and 9,930
outward rays, with no OPEN cases and at most 117 steps to a certificate.
An OPEN result would be reported as unresolved, not divergent.

Reproduce exact graph novelty offline
------------------------------------
    python3 scanner/compare_novelty.py /path/to/candidate.tm \
      current_census/frontier_tables --output /tmp/novelty.json

This compares full canonical tuples. It allows arbitrary working-state
renaming, every spanning root, global reflection, global symbol exchange,
and arbitrary final write/move effects on transitions into halt. The symbol
exchange is a stronger structural-novelty check, not a zero-blank semantic
equivalence. Graph novelty alone does not establish mathematical correctness
or material algorithmic novelty.

Reproduce the complete current corpus scan
-----------------------------------------
With a checkout of the pinned repository:
    python3 scanner/audit_current.py --repo /path/to/ProveIt \
      --output /tmp/rebuilt-pa-census

The scanner checks HEAD against the pinned commit and verifies every tracked
candidate file against its Git blob SHA-1. It reads the requested PA and
docs/incoming paths, including nested ZIP payloads, recognizing the explicit
forms documented in literal_inventory.py and json_inventory.py. It excludes
unexecuted source generators and prose-only tables. A summary count is never
interpreted as a count of established consistency theorems.

Provenance
----------
The scanner modules and broad exact-novelty checker were copied from
docs/incoming/pa194_ax11_research_2026-11-14.zip at the pinned commit,
under pa194_ax11_research_2026-11-14/comparison/scanner/.
Their prior attribution traces the recognizers to the Q-radix packet.
The current adaptation updates the pinned commit and adds scan-progress
output; recognition/canonicalization semantics are unchanged. Original
licenses are retained in scanner/. The new short literal replay checker
classify_193.py is independent code written for this audit. It imports only
the basic five-column parser, not prior simulation or runtime engines.
The combined replay_audit.py is also new independent code. It contains its
own parser, simulator and exact canonicalization, using lexicographic prefix
pruning to accelerate comparisons. It passed against all recorded canonical
fingerprints and complete per-start records, as well as the previous,
separately replayed full-tuple novelty result.
variant193_manifest.json is the unchanged source-locator manifest from the
latest QN6 packet's research/physical_search/variant193/manifest.json.

Evidence boundaries
-------------------
The 194-class status labels attribute the historical packet evidence and
do not announce newly replayed full consistency proofs. The ordinary PA
calibration arguments and unfinished end-to-end iPRA/Lean status are
separately described in comparative_findings.txt. The 52 rejected physical
193 tables are fixed historical objects; the finite certificates say nothing
about every possible repair or every possible smaller consistency machine.

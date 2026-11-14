PA-machine corpus comparison
===========================

Pinned repository: VladimirReshetnikov/ProveIt
Commit: 1c9524d8bf2e0a27b9a16ff622359927f536e663
Scope: Computability/BusyBeaver/Research/PA and docs/incoming.

The delivery ledger covers 61 filed research archives and 11 incoming ZIPs,
for 72 deliveries. The source tree also contains proof-development directories;
those directories are not automatically additional machine designs.

Main findings
-------------
The fresh structural census has 83 distinct fingerprints at 194 working
states, of which 82 have a root reaching the entire transition graph and one
is a disconnected diagnostic fixture. Reflection merges none of these 83.

Historical evidence categories, not new correctness certifications:
  40 reported principal constructions
   7 supplementary constructions
  25 research auxiliaries (including source-tree rotations)
   4 research seeds
   6 rejected designs
   1 diagnostic control

The same scan recognizes 53 stored 193-state tables. They include the known
inconsistent coefficient-three calculus, the runtime-only marker quotient,
and unsuccessful startup/relay transplants. Their presence does not establish
a valid 193-state blank-start machine. See tables193_status.json.

The current PA/README.md explicitly says that neither machine-specific
direction of the iPRA consistency equivalence has been established for its
primary PA194, original PA195, or PA196. Incoming packets claim ordinary
written PA calibrations and explicitly distinguish those from an iPRA proof.
This inventory does not fill that mathematical gap.

Files
-----
packet_ledger.csv/json      All 72 deliveries and their reported results.
frontier194.csv/json        All 83 current 194-state fingerprints, design names,
                           mechanisms, evidence categories, and locators.
annotated_summary.json      Compact checked counts and category breakdown.
tables193_status.json       Provenance and rejection/status notes for 193 tables.
tables.csv/json            Every recognized table occurrence and exact hashes.
classes.csv/json           Fingerprints with all associated occurrences.
representatives/           One literal representative per fingerprint.
catalog_recheck.json       Fresh identity/count check of all 535 representatives
                           in the repository's official MACHINES.tsv.
archives.json              Nested archive identities and duplicate references.
incoming_downloads.json    Exact SHA-256 and byte counts of all 11 incoming ZIPs.
summary.json               Recognizer counts and explicit scope limitations.
parse_errors.json          Empty for the .tm files in this pinned corpus.
inventory.py              Standard-library census implementation.

Reproduction
------------
With the pinned repository materialized locally:

  python3 inventory.py /path/to/ProveIt /new/output-directory

The source files and complete ZIPs must be available; the script does not
download repository data. It never mutates the repository. Existing tables.json
in the output directory is used only as a structural-classification cache;
use a fresh directory for a completely cold replay. The evidence categories
in frontier194 and the packet summaries are editorial annotations, not outputs
of the structural algorithm.

Recognition and equivalence
---------------------------
Recognized literal encodings are complete five-column binary L/R tables in
.tm/.txt/.tsv/.csv. Explicit JSON encodings include textual tables, five-column
row arrays, paired and flat action arrays, numeric-state dictionaries,
transition-key dictionaries, and row records. Signed moves are normalized.
One-state JSON fragments are excluded. The recognizer does not execute
arbitrary source programs or unmaterialized parameterized generators.

ZIPs, including retained nested ZIP payloads, are inspected recursively.
Repeated identical nested archive bytes are represented by duplicate_of links,
not expanded repeatedly. The repository's removed duplicate machine files are
accounted for by its existing MACHINE_FILES.tsv and OMITTED.tsv; they are not
invented as additional stored files in this census.

A rooted fingerprint discovers controls from the designated start by reading
bit 0 before bit 1, then hashes the resulting action sequence. A start-free
table fingerprint is the least such hash among roots reaching the maximum
number of states. When a spanning root exists, equality means isomorphism of
the complete deterministic action graphs up to control renaming, subject to
the usual negligible hash-collision qualification. Without a spanning root,
only maximal reachable components are identified; these objects are flagged
and must not be called complete graph classes. Halting destinations are
identified as terminal, while their write and movement effects are retained.

Designated starts are recorded separately. A comment declares a start; absent
one, 0 is only a convention for dense tables. A native table's start may be
stored elsewhere in its research packet. A start-free graph fingerprint is
never a theorem about the designated blank computation.

The broader census contains small test objects and explicit JSON fragments,
so its total count is intentionally not a count of consistency-machine
designs. The 194-state comparison and its categories are the relevant frontier.

Attribution
-----------
Original machine tables and research mechanisms are from Vladimir Reshetnikov's
ProveIt research packets and their credited antecedents, including James Chang
and Andrew James Wade. The catalogue conventions follow PA/docs/machine_classes.py.
The 77 historical frontier names/categories are attributed to the current QH5
packet's comparison/frontier194_all.json and matched to freshly parsed tables.
The six newer principal names/categories were checked against their current
incoming READMEs and exact dense table hashes. The new census implementation,
current snapshot merge, reflection check, catalogue replay and evidence-status
separation were performed for this comparison. Historical machine proofs and
certificate suites have not all been independently reproved or replayed here.

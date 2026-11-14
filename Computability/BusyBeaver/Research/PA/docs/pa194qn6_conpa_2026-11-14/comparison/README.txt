PA machine corpus census and comparison
======================================

Source: https://github.com/VladimirReshetnikov/ProveIt
Pinned revision: 2337ce611a26e308697ccbddb2a1636f989f01c3
Scopes: Computability/BusyBeaver/Research/PA and docs/incoming

This directory is a reproducible literal-table census plus a source-attributed
comparison of all 61 filed delivery packets and all five current incoming
archives. It is not a claim that every recognized table implements Con(PA).
The corpus includes failed candidates, components, diagnostic fixtures, parent
machines, search seeds, and repeated copies of earlier results.

Principal results
-----------------
21,022 tracked blobs; 1,832 recognized literal table occurrences; 670 distinct
table byte forms; 666 distinct labeled transition lists; 576 maximal-component
buckets. Of those buckets, 567 have a graph-spanning root, and 563 have both a
graph-spanning root and exactly one rowless halt label. There are 76 full
194-state graphs, 22 full 195-state graphs, and 103 full 196-state graphs.

There are two full 193-state graphs, neither an established blank-start
consistency machine. The coefficient-three graph refines an inconsistent
numerical calculus. The runtime-only contraction has source contracts but no
admissible blank startup among the tested starts. A further nominal 194-state
bucket contains disconnected padded test controls and is not one of the 76.

The historical evidence categories assigned to the 76 graphs are: 34 supported
packet constructions, seven supplementary constructions, 30 auxiliary or seed
graphs, and five rejected graphs. These categories attribute supplied evidence;
they are not fresh proofs of 76 machine-specific PA theorems.

Files
-----
summary.json: counts, recognition scope, and exclusion audit.
tracked_files.tsv: every tracked source blob in scope, with Git ID and size.
table_occurrences.json/.csv: every recognized table occurrence and provenance.
table_classes.json/.csv: maximal-component buckets and occurrence lists.
archives.json: recursively inspected archive occurrences.
large_json_audit.json: completion of all first-pass large-JSON exclusions.
frontier_193_194.json/.csv/.tex: named and attributed frontier comparison.
frontier196_evidence.json/.csv: mapping to the historical 90-class 196 audit.
packet_ledger.json/.csv/.tex: all 66 deliveries and their reported contribution.
comparison_notes.txt: narrative explanation, duplicate identities, proof limits.
attributed_frontier194.csv: frozen historical evidence attribution source.
frontier_tables/: raw representatives of the 193/194 frontier buckets.
novelty_corpus.json: frozen exact canonical tuples for all 78 full 193/194 graphs.
check_novelty.py: candidate comparison under the enlarged equivalence below.
novelty_positive_control.json: an existing machine correctly matches its class.
portable_comparison_receipt.json: five comparison artifacts replay byte-for-byte.
audit_qn6.py and independent_qn6_audit.json: independent exact Q6->QN6 row/source binding.
independent_qn6_review.txt: mathematical review of the new composition and edge cases.
AUDIT.md: exact scope, identity convention, proof boundary and known limitations.

Reproduction
------------
Requires Python 3.10+ standard library and Git. A repository containing the
pinned tree and its blobs is sufficient; no network access is needed when those
objects are already available. Scripts read the source repository and never
change it. They may use verified worktree bytes when present, or Git blobs when
the sparse checkout omits a file.

Run from this directory, choosing a fresh output directory:

  python3 scan_current.py /path/to/ProveIt --output /tmp/pa-census-replay
  python3 scan_large_json.py /path/to/ProveIt --census /tmp/pa-census-replay
  python3 build_comparison.py /path/to/ProveIt --census /tmp/pa-census-replay
  python3 check_novelty.py --base /tmp/pa-census-replay --freeze

scan_current.py defaults to the pinned revision. The supplementary scan must
follow it: 35 first-pass excluded JSON paths (10 distinct payloads, at most
18,232,284 bytes) were all inspected and yielded no additional tables. The
completed summary has no unresolved size or nesting exclusions. The first
script's scan counters describe its first pass, not all supplemental JSON reads.

build_comparison.py is intentionally pinned: its human-attributed semantic
categories concern this exact corpus. It obtains the prior frontier CSV and
delivery README files directly from that Git tree, so no prior extraction or
the original working directory is required. The generated JSON/CSV ledgers
reproduce the counts and attributions; the bundled TeX ledgers are presentation
exports. The 196 evidence mapping and narrative notes are separately reviewed
frozen artifacts, not newly proved by running the literal recognizer.

Candidate novelty can be checked without any Git checkout using the bundled
tables and frozen tuples:

  python3 check_novelty.py /path/to/candidate.tm

It compares full tuples, allowing arbitrary control renaming, every possible
graph-spanning root, global tape reflection, global symbol complementation,
and ignoring the final halt-edge action. A negative match result means finite
structural novelty within this recognized pinned corpus. It is not a universal
priority claim, proof of semantic novelty, or state lower bound. Regenerating
the frozen tuples with --freeze replays the canonicalization from the raw tables.

Independent new-candidate audit (requires the pinned repository):

  python3 audit_qn6.py /path/to/ProveIt /path/to/qn6

This replays the exact one-row Q6 splice, 19-instruction source deletion,
unchanged N6 fixed controls, 83 Q source changes, and the flat exchange proof.
It imports none of the candidate builder/compiler/command-checker modules.

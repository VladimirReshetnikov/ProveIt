PINNED CORPUS AND GRAPH COMPARISON

Repository: VladimirReshetnikov/ProveIt
Commit: 1e407ae841e4666f932777fad977ba784ebbcfd5

packet-ledger.json describes all 41 placed PA/docs packet directories and all five current incoming archives. Source-site counts and historical verification claims in its summaries are report-derived. The literal and graph counts below are independently recomputed.

GRAPH FIXTURES

graph-fixtures.json and tables/ retain one complete normalized representative of each of 28 prior 194-state action-graph classes. This includes principal, auxiliary, and rejected tables; it is not a list of 28 independently established consistency theorems. HA-candidate.json and HAZ-candidate.json hold the two new candidates separately. Normalized starts are supplied in JSON: several tables use start 68 or 67, while dense supplied tables use start 0. Never assume every normalized table starts at zero.

Run: node verify-corpus.js

The checker verifies written transition-table digests, exact graph encodings, pairwise distinct prior classes, and absence of both candidate graphs. It considers every root that reaches all declared controls, arbitrary control renaming, tape reflection, global symbol complement, and their combination. Graph comparisons are exact-string comparisons; SHA256 records are identifiers.

CORPUS COVERAGE

The eight prior classes in the placed directories and twenty further classes in the five incoming archives are represented. The archive scans include complete five-column binary numeric tables in .tm and .txt files. Arbitrary program encodings, unmaterialized parameter variants, and every intermediate state of heuristic searches are not claimed to have been enumerated. Archive reports, source construction descriptions, and relevant search families were also inspected.

The initial H candidate was rejected for novelty after its exact native bytes were found at pa194N_conpa_2026-11-13/research/physical/inputs/MPH.native.tm. That graph is retained as the prior fixture MPH. This is why checking only the principal report appendices would have been insufficient.

DIRECT FILE CENSUS

raw-tables/ retains all 618 distinct literal Git blobs from direct .tm files in the 41 placed packet directories. Each filename is its Git blob SHA1. direct-tm-file-manifest.json gives the raw SHA256 and source paths. It also retains non-.tm aliases for the same bytes; the direct census explicitly filters .tm paths.

Run: python3 check-census.py

This verifies Git blob identity, raw SHA256, parser validity, and the census: 2423 direct .tm occurrences, 618 byte forms, 617 recognized complete binary tables with one undefined halt target, occurring 2420 times. The excluded four-state synthetic fixture has no undefined halt target. No recognized direct table has 7 through 193 working controls; this is a file observation, not a lower-bound theorem.

Run: node census-all-direct-graphs.js

Of the 617 recognized blobs, 616 have a root reaching every declared control and form 446 graph classes under the stated symmetries. The remaining six-state offset-control fixture has no such root. direct-graph-census.json retains memberships and per-state counts.

ARCHIVE EVIDENCE

N-archive-full-census.json, R-archive-census.json, Q-JD-radix-archive-census.json, and Q-JD-radix-text-census.json record the five incoming scans. The six- and nine-state archive examples are diagnostic control fixtures. N-archive-193-194-census.json is an earlier independent Wolfram extraction check for the same N archive. No N or R archive remains unread.

The candidate PA-calibration proofs and universal physical checks are separate from this inventory. Neither file counts, graph novelty, nor finite startup tests establish PA consistency or infinite nonhalting by themselves.

COMPLETE UNION ACROSS ALL WORKING-STATE COUNTS

combined-source-manifest.json joins the direct corpus and all five archive scans. raw-tables-extra/ adds only the49 byte forms not already among the618 direct blobs. The collection scan includes .tm,.txt,.csv,.tsv candidates and accepts only complete five-column numeric binary tables.

Run: node check-combined-corpus.js

This standalone replay reads retained bytes and exact source-locator memberships. It verifies667 complete numeric byte forms in3600 source-file occurrences. One four-state, zero-halt-target fixture occurs3 times and is excluded from the one-halt recognizer. The remaining666 forms occur3597 times. Excluding the six- and nine-state diagnostic fixtures that have no spanning root,664 byte forms yield476 exact graph classes. The194-state subset has51 byte forms in261 occurrences, representing28 classes. Larger graph families and all memberships are retained in combined-corpus-census.json. All counts exclude the new HA and HAZ candidates.

final-inventory-summary.json is the compact authoritative count summary; design-status.json distinguishes reported constructions, audited auxiliaries, search inputs, and rejected experiments, with each representative source locator and normalized table/hash identities.

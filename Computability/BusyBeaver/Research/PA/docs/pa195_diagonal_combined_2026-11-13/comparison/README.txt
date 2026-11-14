ARCHIVE COMPARISON AND FINITE GRAPH NOVELTY CHECK

Scope and provenance
--------------------
This comparison is fixed to VladimirReshetnikov/ProveIt commit
5ed5a41fa5932433111eea096311364c6087e8e3. It covers every incoming ZIP
at that commit, recursively, and every literal .tm file in
Computability/BusyBeaver/Research/PA. Within archives it also recognizes
strict numeric, five-column binary tables in .txt, .tsv and .csv files.
It does not execute submitted code or recover arbitrary tables embedded
in program source, JSON or prose. The narrative comparison also reads
the reports and identifies explicitly rejected constructions.

The census scans each byte-distinct ZIP payload once. Thus its 2,363
table occurrences count members of unique payloads plus repository files,
not every duplicated route through an embedded archive. It finds 45
distinct ZIP payloads at 73 encountered archive locations, within 32
top-level ZIP files. The maximum nesting depth is eight.

There are 583 distinct table byte strings and 573 distinct labeled
transition functions. Of these, 571 labeled functions have a working
vertex reaching every working state; their root-free action graphs form
422 classes. Two disconnected synthetic controls, with six and nine
working states, are recorded separately. The 422 classes include a
four-state synthetic control, experiments, ancestors and rejected
tables. These counts are not counts of successful consistency machines.

Contents
--------
archive_comparison.json / .csv
    All 32 top-level archives, with exact SHA-256, direct member count,
    main contribution, and claim status. These descriptions are curated
    from the reports; a report-positive entry does not certify a new
    kernel-checked PA biconditional.
census_summary.json, root_free_summary.json, root_free_unclassified.json
    Compact census totals and the two disconnected controls.
graph_classes.json / .csv
    All 422 graph classes. JSON includes every labeled transition
    function, raw table hashes, source/member paths and enclosing archive
    hashes. CSV gives one representative provenance row per class.
all195_graphs.json
    The nine prior 195-state graph classes and their literal occurrences.
    Three correspond to the positive PA195, 195S and 195C constructions;
    six are rejected diagnostics.
novelty_receipt.json, novelty_replay.json
    Independent finite graph checks of the delivered diagonal-plus-
    Combined195 table. The replay is produced by verify_novelty.py.
calibration_review.txt
    A skeptical mathematical review of the original PA195 calibration.
    It found no concrete mathematical gap; it is not a formal proof.
LICENSE.ProveIt.txt
    License of the upstream source snapshot.

Canonicalization and its limits
------------------------------
For each possible working root that reaches every working state, visit
the deterministic transition graph in breadth-first order, considering
read-bit zero before read-bit one. Record each edge's write bit,
direction and numbered successor; terminal successors are represented
by -1. Choose the lexicographically least resulting word and SHA-256 its
compact JSON encoding. This is an isomorphism invariant for these
action-labeled graphs, independent of working-state names and designated
initial state. A graph without a spanning root is reported separately.

The novelty replay also compares the new graph after left/right mirror,
global symbol complement, and both. Symbol complement includes changing
the read and write symbols; it is used only as a conservative graph
novelty check. It does not assert equivalence of machines on blank-zero
tape. Distinct canonical hashes demonstrate absence of an action-graph
isomorphism within the enumerated corpus. This check cannot prove
nonhalting, arithmetic consistency, or equivalence of algorithms.

The complete raw-table corpus is intentionally omitted (approximately
9 MB uncompressed). Its exact origins and hashes are in the manifest;
the following commands regenerate it from the pinned public repository.

Reproduction (Python standard library only)
------------------------------------------
From the root of this extracted deliverable, with a complete checkout of
the pinned ProveIt repository at ../ProveIt:

    python3 comparison/census.py ../ProveIt replay_census
    python3 comparison/graph_census.py replay_census
    python3 comparison/build_graph_manifest.py replay_census replay_comparison

census.py refuses a repository whose git HEAD differs from the recorded
pin. This ensures the summary is not silently labeled with another
commit. Both Research/PA and docs/incoming must be present in the checkout.

To check the delivered table (replace the path with the table location):

    python3 comparison/verify_novelty.py path/to/machine.tm --start 0

To compare against the freshly regenerated class manifest instead:

    python3 comparison/verify_novelty.py path/to/machine.tm --start 0 \
        --manifest replay_comparison/graph_classes.json \
        --output replay_novelty.json

The default manifest is comparison/graph_classes.json, located relative
to the verifier script. All scripts accept ordinary relative paths.

Code provenance
---------------
census.py is adapted from inventory/inventory.py in the supplied
PA195_ConPA_research_2026-11-14.zip. This version broadens strict numeric
table recognition and adds a pinned-HEAD check. graph_census.py,
build_graph_manifest.py and verify_novelty.py implement the independent
graph comparison performed for this deliverable. The curated archive
descriptions and mathematical review are new research notes.

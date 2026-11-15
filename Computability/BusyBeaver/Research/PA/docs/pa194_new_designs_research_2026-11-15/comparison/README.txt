PINNED PA DESIGN COMPARISON
===========================

Snapshot and scope
------------------
All counts refer to ProveIt commit
793c68737d94bffa4e32a75bce6cc8058d6d22f0.

The attributed roster contains 83 distinct named principal/supplementary
194-state graphs, organized into 31 mechanism families. There are 93 filed
packets and four current incoming archives, hence 97 deliveries. The filed
747-class catalogue is retained byte-for-byte; its identities were checked
again against raw files at the exact pinned GitHub commit.

The four incoming ZIPs were scanned recursively using the retained numeric
text and explicit-JSON recognizers. There are 2711 inspected non-ZIP payloads,
9 ZIP references to 6 distinct ZIP byte payloads, 1757 table occurrences,
875 normalized labeled tables and 723 single-terminal table classes. The
union with the filed catalogue has 1137 catalogue keys. All 520 spanning
194-state classes have complete literal representatives. Their roles are
83 named designs, 419 research auxiliaries, 14 rejected classes and 4 seeds.
None of these counts means that 520 consistency theorems were established.

The separate outside-PA/docs audit retrieves 126 explicit-table-capable
tracked inputs: 14 .tm, 97 .json, and 15 .txt files. Each byte payload is
checked against its pinned Git blob identity. They yield 14 recognized
occurrences, 13 normalized tables and ten classes already represented in
the filed/incoming union; their working counts range from 196 to 209.

Arbitrary generators, Lean definitions, prose-only encodings and opaque
binaries are outside the explicit-table recognition rule. The filed corpus
is accounted for by the pinned delivered catalogue rather than a new parse
of every historical representation. Diagnostic catalogue keys can describe
maximum reachable subgraphs; the 520-class frontier is graph-spanning, so
that limitation does not affect the new-machine comparison.

Files
-----
named_designs83.csv/json       Every named design, aliases and mechanism.
family_comparison31.csv/json   The 31 mechanism families and proof obligations.
packet_ledger97.csv/json       All 97 delivery summaries and source locations.
frontier520_annotated.csv/json Full 194-state frontier with attributed roles.
census/representatives/       All 723 literal class representatives.
census/                       Occurrence, archive, normalized-table and class ledgers.
catalog/                      Exact pinned filed catalogue and classifier.
source_identities.json        Pinned catalogue identities and URLs.
incoming_identities.json      Four exact current incoming identities and URLs.
support_inputs/               Exact 126 additional PA byte payloads.
support_scan.json             Their classification and identity receipt.
support_trees.json            Pinned Git tree evidence for selection completeness.
licenses/                     Retained inherited notices.

Offline verification
--------------------
Use Python 3.10 or later, standard library only, with assertions enabled.
From the enclosing archive root:

  python3 -B comparison/verify_corpus.py --output corpus_replay.json
  python3 -B comparison/novelty_check.py \
    construction/candidate/machine.tm mp_construction/candidate/machine.tm \
    --output novelty_replay.json
  python3 -B comparison/check_new_pair.py \
    mp_construction/candidate/machine.tm construction/candidate/machine.tm \
    --output pair_replay.json

The offline verifier reclassifies all representatives and recomputes the
greatest immediate-action congruence on all 520 frontier tables. Every one
has 194 classes. The novelty checker uses explicit bijections and literal
rows, trying every corpus root and arbitrary state names, reflection,
global symbol exchange and ignored terminal-entry actions. Symbol exchange
is an additional structural comparison, not a zero-blank semantic theorem.
Hashes bind inputs; they do not replace the bijection comparisons.

Optional source rebuild
-----------------------
Obtain the four ZIPs named in incoming_identities.json from their exact
pinned URLs, retaining their filenames. Then run from the enclosing archive
root, in a copy of the delivery:

  python3 -B comparison/current_census.py --archive-dir /path/to/four-zips
  python3 -B comparison/rebuild_ledgers.py --archive-dir /path/to/four-zips
  python3 -B comparison/scan_support.py
  python3 -B comparison/verify_corpus.py

The first two commands require the four original archives, omitted here to
avoid unnecessary duplication; they check every original top-level Git
blob identity before use. The third command is an optional online audit
of the exact pinned PA tree and its 126 selected blobs. None is needed to
reconstruct either new positive machine from its supplied construction.

Recovery provenance
-------------------
This component was faithfully reconstructed after volatile working storage
was reset. It uses the same exact four pinned archives and catalogue, and
freshly reproduces every previously reported census count. The 83 names
come from the retained 74-name supplied annotated roster plus the nine
current named designs. Its 31-family taxonomy retains 27 supplied groups
and adds the four identified incoming combinations. Reconstruction scripts
and fresh receipts are included, rather than claiming byte identity for
the lost derived ledger formatting.

Attribution
-----------
literal_inventory.py, json_inventory.py and stream_json_tables.py are
retained from the pinned loop-return package's census tools. The official
machine_classes.py is retained from the pinned filed catalogue. The source
programs and mathematical calibration remain the attributed predecessors;
this comparison assigns no new proof status to a table solely from scanning.

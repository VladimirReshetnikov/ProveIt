LATE SNAPSHOT RECONCILIATION

Checked at 2026-11-15 01:05:04 UTC.
Original research snapshot: 8d31445d858761a8f6150c2e5012adae8895e932
Late repository snapshot:  ef0839bf15d8b556bc1e1634e6ad310adbcd4fe3
Placement commit:          78080fb26db69fed2ee295332cfdc16eafae1c7d

Result
------
The late catalog has exactly the same set of 747 canonical table-class keys as
our original 705 filed classes united with the six incoming archives. Its 139
classes in the spanning 194-state bin are exactly those covered by the frozen
139-table frontier. The additional disconnected 194-control diagnostic remains
represented in the latest catalog under its reachable-state count. No original
count or novelty claim needs to change.

The six incoming archives have been filed under PA/docs. Their paths are mapped
in ../late_snapshot_paths.csv. The fresh pa194_research_2026-11-14.zip delivery
was filed with the suffix _2; the archive whose name contained (1) was filed with
the suffix _1. frontier_current_paths.csv maps all 140 frozen representatives
to their latest catalog representatives.

All 13,879 original historical member records are unchanged. The latest six
packet records total 1,438, versus 1,439 direct .tm members in the frozen input
archives. The single absent occurrence is:

  loop packet, comparison/representatives/
  d5fabd960755e1d801cc865a7d0c047dd2c3bf0394bc4aca4a99d87ba295f990.tm

Its byte SHA-256 is
  e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8
and its canonical table class is
  032cf6af180930a9b7bb3f36716eb225bec9332bdd6f67b535354fa9fbef176c.
This is a 196-state PA196 table. Its class remains in the latest catalog, with
108 listed member occurrences. We identify the missing member record exactly;
we do not infer why it was omitted. It has no effect on either class-set match
or on the 194-state novelty comparison.

Reproduction
------------
From any working directory, run this script by its path:

  python3 comparison/late_snapshot/verify.py

All inputs are frozen locally. The script validates the byte SHA-256 and Git
blob identity of all four latest source files, checks the complete class sets,
checks the frontier, and reconciles per-packet member payload multisets. It
writes ../late_snapshot_receipt.json by default; --output PATH selects a
separate receipt location. The top-level reproduce.py uses that option to
preserve the frozen release. verification.log records a passing run.
source_identities.json supplies exact pinned raw URLs for independent retrieval.

Scope
-----
The original comparison/audit.py reclassifies all 140 literal representatives
and checks the original frozen census. This late check compares the repository's
pinned canonical class keys and member ledger against that audited inventory.
It does not fetch and reclassify every newly filed physical table. In particular,
canonical catalog equality is not a new mathematical calibration theorem or a
claim that every cataloged machine is a valid consistency machine.

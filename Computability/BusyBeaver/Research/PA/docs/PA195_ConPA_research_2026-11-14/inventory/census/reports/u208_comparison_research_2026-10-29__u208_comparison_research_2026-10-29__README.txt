Comparing the 208 state proposals and searching below 208
========================================================
Research prepared for Vladimir Reshetnikov, 29 October 2026.

RESULT: The requested fewer-than-208-state target was NOT achieved.
This package is an honest comparison and proof-search research report, not a
new accepted machine, not a proof of 208-state minimality, and not a proof-
assistant certificate. The 207-state exploratory table is expressly REJECTED
as a universally correct canonical-step interpreter: a complete finite-frame
counterexample is supplied. It is not a blank-halting counterexample.

Read report/report.pdf or its full TeX source report/report.tex. The report
compares five pinned archives (nine machine outputs) and proves they represent
two existing rooted action-labelled graph classes. It records new macro,
source and local table search outcomes, a concrete failed repair, a proved
weak/exact schema equivalence, and the unresolved PA/equality/runtime bridge
for a costed theory replacement. Source DAG counts are NOT TM state counts.

FAST REPRODUCTION (Python 3 standard library only)
  python3 verify.py --manifest --negative-controls
  python3 -O verify.py --manifest --negative-controls
The checker uses no assertions and executes no downloaded/supplied scripts.
It recomputes all native/dense row equalities, all 3,744 conjugacy equations,
complete 48,140-step startups, and the 568/538-step first FULL canonical-return
witness, including valid zero-padded source leaves and all register/spare
blocks. Original audit PC notation omits trailing zero cells; the report
also gives the resolved parent leaf ending in a zero.

PDF REBUILD
  python3 build_report.py
Requires pdfTeX, Latin Modern and ordinary LaTeX packages. No shell escape;
format/font-map caches are generated in a writable temporary directory.

SELECTED RESEARCH REPLAYS
  python3 replay_searches.py
Compiles newly authored C++ text into a temporary directory, replays ternary
source abstraction and the macro positive control, and checks deterministic
results. Use --all for full selected C++ searches (a few minutes, machine-
dependent). Program outputs are evidence of bounded search, NOT lower bounds.

CONTENTS
  machines/             deduplicated literal native and dense input tables
                        plus expressly rejected207.native.tm
  sources/              two current source maps and rejected candidate map
  evidence/             comparison index, witnesses and selected audit receipts
  provenance/           commit pin and exact original ZIP identities
  search/table/         new bounded local searches, raw contexts and receipts
  search/macro/         two-sided macro searches, raw contexts, positive control
  search/source/        selected source-only measurements and owned macro data
  search/theory/        theory investigation notes, no copyrighted paper copy
  checks/               original owned checking sources for provenance;
                        these historical utilities may use workspace paths
  verify.py             standalone independent checker, no workspace paths
  MANIFEST.json         exact SHA-256 ledger of every other release payload file

Only selected data and source text are included; no compiled executables,
large incoming ZIPs, duplicate historical PDFs, or withdrawn reports appear.
Friedman's lecture is linked in the report, not redistributed. The old approved
208-state calibration is inherited and explicitly scoped; this package does
not rederive its entire original proof-search implementation.

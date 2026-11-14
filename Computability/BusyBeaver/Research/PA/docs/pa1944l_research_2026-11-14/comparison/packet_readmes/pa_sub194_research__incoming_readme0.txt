SEARCHING BELOW 194 STATES
Comparison, exact finite searches, and an immediate-MP-halting prototype
November 14, 2026

RESULT
======
The requested bound was NOT achieved. This archive contains no verified
machine with fewer than 194 working states. The new literal construction,
MP196, has 196 working states. It is three states above the largest count
allowed by the request (193), and two above the prior 194-state frontier.
Failed searches in this archive do not establish a lower bound.

Read report/pa_sub194_research.pdf first. The report includes the complete
transition table, mathematical command/source arguments, proof boundaries,
a 43-class frontier comparison and the complete 56-delivery ledger.

SNAPSHOT AND SCOPE
==================
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 2a88cb6a3f823e0de5addf19d725bf8373860c71
Scope: PA research tree; all 51 filed PA delivery directories; all five
active incoming ZIPs; retained historical nested ZIPs. Related ZFC and
ConciseIPRA methods were read selectively, not exhaustively inventoried.

The numeric-table recognizer found 1542 occurrences, 731 byte forms,
503 spanning action-graph classes and two disconnected diagnostic classes.
At 194 states: 43 graph classes = 28 reported constructions + 10 auxiliary
classes + 5 rejected classes. Class counts are not correctness claims.
Start controls are ignored only in duplicate classification; a literal
machine theorem always retains its prescribed blank start.

MAIN CONSTRUCTION
=================
machine/machine/machine.tm is the dense MP196 table:
  working states 0..195; initial 0; separate halt label 196;
  392 binary left/right transitions; all-zero two-way tape; head at 0.
Dense SHA-256:
c14cc614c8f33a67697b4fbc3b502ee5c8c6b3764ef721cd1e0c09f3810a97f3

Native SHA-256:
7689bf1cf5843f3f2c27ac3e3f7da2a84b28a8bce1d9f6458209579012ef6271
Native start 74, halt 254. Only inherited row (164,1) changes, to 1 R 400.
The four added rows are:
  400 0 0 R 130
  400 1 1 R 401
  401 0 0 R 63
  401 1 1 R 68
The baseline and its hash are bundled in machine/inputs/.

Successful MP halts immediately on conclusion 1. Other successful MP
returns its conclusion, leaves the formula stack unchanged and clears the
offset. Failed MP returns truth with the proposed offset. AX is unchanged.
The original Shift guard remains, but no formula field or canonical stack
entry equals 1 at a completed nonhalting command boundary. That arithmetic
invariant, independent of consistency, excludes the old Shift halt.

The exact source resolves 3663 sites and all 4768 primitive outcomes.
The complete blank initialization ends at the required clean frame after
58154 transitions. The package also checks 478 finite command cases.
An independent finite checker verifies every native/dense startup step,
the complete tape and the new source success block.

PROOF STATUS
============
The new command compiler and controller have ordinary mathematical proofs
and executable checks. The overall PA-equivalence argument inherits the
attributed numerical-calculus calibration and generic arithmetic-block
lemmas from the source corpus. The symbolic runtime uses those block
contracts; it does not independently prove them. No new end-to-end Lean,
Rocq, or iPRA endpoint is included. The report distinguishes these facts
from bounded testing and from the repository's incomplete iPRA endpoint.

The abstract total-Shift protocol is correct from all stores for its
compiler identities. Its literal simulation is asserted on initialized,
invariant-preserving runs. Soundness starts with theorem-annotated stores;
arbitrary stores are used for completeness, not for an unconditional
soundness claim. The invariant holds at completed command boundaries:
MP can temporarily write 1 while performing its final internal comparison.

OFFLINE CORE REPLAY
==================
Run these commands from the top-level extracted directory. Python 3.10+
and its standard library suffice. Do not use Python -O or disable asserts.

  python3 -B protocol/check_mp_positive.py
  python3 -B machine/build.py --output generated/machine
  python3 -B machine/independent_review/check.py machine
  python3 -B search/history/check_controls.py

The first checker handles both the unshifted and positive-target abstract
protocols despite its historical filename. The delivered machine uses the
unshifted protocol. Recorded command-check totals: 35 symbolic identities,
130 exact integer checks, 419 scheduler-code examples.

The builder recreates the table and its source binding from bundled inputs.
Its default output is machine/generated; the explicit path above keeps
fresh replay output outside the frozen machine/ directory.

LOCAL SEARCH REPLAY
===================
See search/encodings/SEARCH_REPORT.md and search/history/README.txt.
The encoding searches additionally need a C++17 compiler. They tested
1195148640 patch trials over eight input machines and three finite templates,
with no survivor. The 43-input history-restoration search tested 177936788
branch-action proposals, with no survivor. A final 17-step history screen
on MP196 tested 4373528 proposals, also with no survivor. These quantities
are template trials, not distinct machines, and are not lower bounds.

search/source/ holds supporting N6 zero/positivity and return-row searches.
Their scope and replay commands are documented there. The source/runtime
contracts in these experiments retain their inherited assumptions.

CENSUS REPLAY
=============
comparison/current_census/ records all recognized occurrences, original
locators, byte hashes, graph membership and recursive ZIP identities.
comparison/packet_ledger56.json and frontier194_annotated.json give the
human classification. The JSON-only PA194N_AD table is included.

A new census needs a checkout of the exact pinned revision and the archive
payloads named in current_census/archives.json. Some historical payloads
are stored in the repository's filed packets; the audit traverses them
recursively. See comparison/audit_current.py --help. The archived audit
results do not require network access to inspect or compare.

REPORT REBUILD
==============
From report/:
  python3 generate_tables.py
  pdflatex -interaction=nonstopmode -halt-on-error pa_sub194_research.tex
  pdflatex -interaction=nonstopmode -halt-on-error pa_sub194_research.tex

All TeX inputs used by the report are included. The inherited calibration
sources in references/calibration/ are historical report fragments; they
retain their original macros, citations and statements about earlier
machines. They are dependencies for the logical calibration, not alternate
claims about the new table.

PACKAGE MAP
===========
report/       PDF, TeX, generated tables, pinned bibliography
comparison/   full packet ledger, frontier annotations, raw census, scripts
protocol/     command proof, symbolic algebra checker, independent review
machine/      exact 196 table, builder, source proof, receipts, review
search/       portable local searches, inputs, results and controls
references/   43 frontier representatives and inherited calibration sources
licenses/     inherited license notices
SHA256SUMS    checksums of final packaged files (except this manifest itself)

Do not infer Con(PA), its negation, or a state lower bound from the presence
of these artifacts. The research goal of a verified machine below 194
remains unsolved by this work.

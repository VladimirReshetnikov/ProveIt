U208: A THREE-CELL FOLD FOR THE CONSISTENCY OF PA
Prepared for Vladimir Reshetnikov, 29 October 2026

RESULT
======
machine/u208.tm is a complete deterministic binary, one-tape candidate with
208 working states (0 through 207) and a separate halt label 208. The tape is
two-way infinite, initially all zero; the start state and head coordinate are
zero. Every row moves L or R. Initialization is included in the 208 states.

The five supplied U209 code archives represent only TWO rooted transition
graph isomorphism classes. Four are the same machine up to state renaming;
Compatibility is the distinct alternative. report.pdf compares all of them,
proves the new deletion completely, explains its proof boundary, and prints
the complete dense U208 table. report.tex is the editable source.

NEW PATCH (JOINT NATIVE LABELS)
==============================
Delete state 211, redirect its incoming targets to 172, and change 172/read0
to write0, moveL, target217. The only changed retained rows are:

  163 0 0 L 211  ->  163 0 0 L 172
  163 1 1 R 211  ->  163 1 1 R 172
  172 0 0 L 67   ->  172 0 0 L 217

Plain uses different native labels: Joint helper217 is Plain helper214.
The final dense table and state map remove that naming ambiguity.

WHY IT WORKS
============
Complete incoming histories prove two facts in the parent:
* state211 scanning0 has predecessor1;
* state172 has predecessor word10.
Four child paths, lengths3,1,7,1, inspect only the current cell and at most
two left neighbors, and preserve the entire tape. All414 ordinary rows
commute with the projection211->172. Positive block simulation proves
halting equivalence from state0 on every common initial tape, with

  T208 = T209 + 2*N(parent211/read0) + 6*N(parent172/read0) <= 7*T209.

No source instruction, source address, numeric encoding, or theory changes.
The new machine equivalence is an ordinary mathematical proof formalizable
in PA. Composing it with the retained U209/calculus/U-to-PA calibration gives
the intended nonhalting iff Con(U) iff Con(PA) endpoint. This package contains
no new end-to-end Lean, Rocq, MM0, or exported PA proof object. It asserts no
unconditional nonhalting, consistency, global minimality, or certified record.

VERIFICATION
============
* All five input quick replays pass; both machine classes fully replayed.
* Two independently implemented finite fold checks pass; eight damaged
  constructions rejected. The local checker also passes under Python -O.
* Fresh U208 universal runtime:5084 arbitrary-value contracts,416/416rows,
  1251865 symbolic inference applications, all duration coefficients valid.
* Exact whole-tape startup:48140 identical steps,120 one-cells,43 spares.
* All208 working states are transition-graph reachable from start0.
These symbolic derivations are executable mathematical evidence, not a
proof-assistant kernel certificate. A finite prefix is not nonhalting proof.

REPRODUCE OFFLINE
================
Python3.10+ and its standard library, with assertions enabled:

  python3 -B reproduce.py

The driver checks all hashes, reconstructs the native/dense tables, runs the
independent checks, compares the input proposals, checks exact startup,
binds borrowed engines and parent data to the retained original archive,
and rederives all5084 runtime contracts. It writes only to temporary paths.
The full runtime phase took about151seconds in the preparation environment.

  python3 -B reproduce.py --quick

The quick command EXPLICITLY SKIPS the fresh full symbolic runtime replay.
It still checks the complete finite fold and startup. To retain a receipt,
use --output /some/path/outside/this/package/replay.json.

To rebuild the PDF, work in a copy and run pdflatex twice on report.tex.
PDF metadata/toolchain can change PDF bytes; literal machine bytes are fixed.

ARCHIVE
=======
machine/     Final208 tables, unchanged source, state map and construction.
baseline/    Exact Joint209 parent and inherited runtime-label map.
code/        Builder, independent checkers, startup and full runtime replay.
comparison/  Exact table/source snapshots of all five input code proposals.
evidence/    Fresh receipts, case records, parent replay logs and comparison.
reference/   Unchanged Joint209 and unary-theory archives, with full lineage.
research/    Rejected-rotation counterexample and bounded search limitations.
provenance/  Pinned commit, original archive sizes, Git and SHA256 identities.
licenses/    Retained inherited licenses and notices. Also see NOTICE.txt.
paper/       Complete dense transition table as editable LaTeX.
SHA256SUMS   Hashes of every other release file.

PRIMARY DENSE TABLE SHA256
=========================
9f4ea95849c5e1d01fa3f740023092230cd7006eed650b94a2d5da537e25212c

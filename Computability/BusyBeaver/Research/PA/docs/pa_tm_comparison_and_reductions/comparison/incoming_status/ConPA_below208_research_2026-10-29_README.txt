SEARCHING BELOW 208 STATES: COMPARATIVE AUDIT AND REDUCTION SEARCH
29 October 2026

RESULT AND LIMIT
================
This dossier does NOT establish a 207-state consistency machine. The requested
later commits already supply 208-state machines. The research here compares and
checks those constructions, extends the reduction search, and proves a new
obstruction to one tempting logical simplification. No rejected or unchecked
table is promoted to an accepted smaller machine.

Read paper/report.pdf; edit paper/report.tex and its three small included TeX
files. The report contains the mathematical arguments, exact comparison, search
scope, verification status, and further research questions.

SOURCE SNAPSHOTS
================
Latest requested ProveIt commit:
  34aaab66fc5dc834863ed00ea84823c93b8c5b1e
Earlier U208 commit:
  ef5a23e04b0285e321ceec5f4b329223cee0ab57
Original U209 intake:
  fe8b3a2d1db0033113e986590f79ecba3e5ef500

All five code-bearing U209 packets represent only TWO rooted machine classes.
The five newer U208 packets give nine presentations of only TWO classes. Every
U208 packet uses the same conditional-history 172/211 identification. They
cannot be combined into an additional deletion. Exact source/table snapshots,
forced bijections, source CFG checks and hashes are included.

NEW RESEARCH IN THIS DOSSIER
===========================
1. A two-element finite model shows that globally identifying the cover emitter's
   source and output roles collapses its intended arithmetic strength. PA proves
   consistency of the collapsed theory, so, if PA is consistent, it cannot retain
   the required PA-provable consistency biconditional with PA.
2. Exact exhaustion of all 279,936 independent parameter permutations in seven
   unrestricted axiom rows gives minimum source DAG size 197, with exactly four
   minimizers. Association and other source instructions are fixed. This is not
   a physical-state lower bound.
3. Both outgoing keeper rows were synthesized over all 21,528 unordered state
   pairs in each 208-state class, including the start-state pairs. Depth 12 and
   bound 71 runs gave no survivor; the same algorithm recovers the known U209
   fold as a positive control. A stronger source-conditioned Class A run also
   gives no survivor.
4. Correlated zero/positive and interval source invariants, all-spares-one
   specialized runtime contracts, row-order/association experiments, and
   shifted-head searches extend the discovery scope. Their exact bounds and
   evidence are in the report and research subdirectories.

FRESH BASELINE VERIFICATION
==========================
Each final U208 class was freshly checked over arbitrary register values:
  Class A: 5,084 guarded contracts, 1,251,865 symbolic inferences, 416/416 rows.
  Class B: 5,084 guarded contracts, 1,250,564 symbolic inferences, 416/416 rows.
The exact 48,140-step blank startup is preserved. All 14 native/dense comparison
presentations were checked, including the older U209 data.

These are ordinary mathematical/inductive executable certificates. The inherited
U/PA calibration is not replaced by a new exported PA, Lean, Rocq, or MM0 proof
object. Finite blank execution is not being used as a nonhalting proof.

OFFLINE REPRODUCTION
===================
Python 3.10+ and its standard library suffice for the default verifier:

  python3 -B verify.py --output /tmp/conpa-dossier-finite.json

It checks MANIFEST.json, all snapshot comparisons (also under optimized Python),
the collision model, the exact rejected-prefix witness, all 279,936 parameter
choices, and the two retained baseline packets' finite certificates. It writes
intermediate work to temporary directories and leaves the release unchanged.
It EXPLICITLY does not rerun the full universal runtimes or long discovery jobs.

To rederive all universal contracts for BOTH final 208-state classes:

  python3 -B verify.py --full-runtime --output /tmp/conpa-dossier-full.json

Allow several minutes. Do not use Python -O for the inherited full symbolic
engines. The small independent comparison/model/permutation checkers use explicit
exceptions and were also exercised with optimized Python.

To rerun the broad two-row discovery screen (requires a C++17 compiler):

  python3 research/two_row/run.py --class control --output /tmp/conpa-control
  python3 research/two_row/run.py --class A --output /tmp/conpa-search-A
  python3 research/two_row/run.py --class B --output /tmp/conpa-search-B

The control must recover the known 172/211 fold. A candidate from any exploratory
search would still need an exact whole-tape simulation proof or a complete new
source/runtime/startup proof. Other replay commands are in research/*/README.txt.

CONTENTS
========
paper/             Complete editable report and compiled PDF.
code/              Independent comparison and finite-model checker.
baseline/snapshots Exact 14 table/source presentations, manifests and notices.
baseline/*.zip     Unchanged Entry Context and U208 research release payloads,
                   plus the unary theory, retaining the inherited proof chain.
research/          Portable new analyses, search code, receipts and a clearly
                   labeled rejected grammar transformation.
evidence/          Fresh checks and pinned intake inventories.
NOTICE.txt         Attribution and proof-status boundaries.
MANIFEST.json      SHA-256 binding of every other release payload file.

To rebuild the PDF, change directory to paper/ and run pdflatex twice on
report.tex. The TeX packages are standard TeX Live packages. Rebuilding may
change PDF metadata; the exact machine tables and source inputs remain fixed.

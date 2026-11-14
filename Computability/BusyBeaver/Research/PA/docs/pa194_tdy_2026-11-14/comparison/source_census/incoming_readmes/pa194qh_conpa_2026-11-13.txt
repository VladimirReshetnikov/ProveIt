PA194QH -- audited 194-state alternative for Con(PA)
Research release, 13 November 2026 (Pacific time)

RESULT
======
The requested reduction below 194 working states was not achieved.
The fallback is a complete new literal 194-state machine, PA194QH, combining
the supplied Q premise-exchanged quantifier emitter with the supplied H
visible-result, no-push modus-ponens controller and cache-only Shift test.
The combination changes emitted formulas and command-store behavior.
Its individual ingredients, compiler, arithmetic engine, decoder folds,
and inherited logical calibration are credited to the supplied research.

The ordinary mathematical theorem proved in report/report.tex is

  PA proves: [ PA194QH does not halt on blank tape ] iff Con(PA).

The proof composes the retained ordinary PA calibration with explicit
formula-proof, command-word, and physical-trace transformations. This is
not a newly compiled end-to-end Lean or Rocq theorem. The executable
symbolic certificates have been replayed in full. A finite simulation is
not offered as evidence establishing infinite nonhalting.

EXACT MACHINE
=============
Definitive table: machine/machine.tm
Five columns: current_state read_bit write_bit direction next_state.
Working states 0,...,193; initial state 0; terminal halt label 194.
Binary tape; two-way infinite all-zero blank tape; initial head coordinate 0.
Every transition moves one cell L or R. There are 388 transition rows.
All 194 controls are reachable in the transition graph. This does not assert
that they are all visited by the blank computation.

Dense table SHA-256:
0f101f654f69230744e8c9aac14a7616745e247855fd964530603ea1ac6412ba

machine/machine.native.tm is the equivalent native-numbered table, with
start 74 and halt 254. machine/labels.json gives the exact label bijection.
The complete transition table also appears in the PDF appendix.

START HERE
==========
report/report.pdf        Main report, proof, comparison, and full table.
report/report.tex        Editable LaTeX source; generated fragments included.
RESULTS.json             Compact machine-readable result and limitations.
verification_release.json  Full five-stage reproduction receipt, all PASS.
PROVENANCE.json          Pinned source commit and attribution boundaries.
SHA256SUMS               Release content hashes (excluding this manifest).

REPRODUCE THE CERTIFICATES
=========================
From this extracted directory, run:

  python3 -B verify_all.py

Requires Python 3.10 or later and the standard library; no network needed.
Do not use -O or set PYTHONOPTIMIZE: assertions are part of the checks.
The wrapper verifies the frozen inputs, reconstructs the machine, checks
the emitter and command identities, audits the source against H, replays
the independent literal-tape checker, and compares all 42 frozen frontier
classes. It regenerates receipts and checks the released table hash.
The independent tape stage took about 74 seconds in the preparation run;
runtime on another machine may differ. Receipt timings are not reproducible
content hashes and will change when verification is rerun.

To rebuild the report with a usual TeX Live installation:

  cd report
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

The third pass settles the contents and long-table references after a clean
build. report/generate_tables.py regenerates report fragments from receipts.
The historical reference manuscripts are retained for inspection; the main
report is the self-contained compilable TeX entry point. The two scoped
Lean excerpts are reference context, not a stand-alone compiled project.

EVIDENCE
========
Allocation: 134 fixed controls + 67 raw axiom readers - 7 folds = 194.
Source: 190 AX macro tokens; 3,653 sites; 4,754 instruction outcomes.
Difference from H: 79 resolved instructions in the exchanged-axiom block.
Physical validation: all 4,754 arbitrary-register outcomes, not just small
numeric examples; arbitrary affine gap and arbitrary finite nonempty spare
list; four list-sweep lemmas re-derived from literal rows.
Independent symbolic operations: 1,125,793; exact complete blank startup:
57,922 steps, including the entire tape and its zero exterior.
Folds: 28 local cases checked in the simultaneously folded final machine.

comparison/ contains all 56 delivery records (51 filed plus five incoming),
the recognized literal-table census, and all 42 existing 194-state graph
class representatives. The 42 comprise 28 reported constructions, nine
auxiliary classes, and five rejected classes; these categories are not
silently treated as completed formal proofs.

The novelty verifier compares full canonical graph tuples under state
renaming, every spanning root, global reflection, bit interchange, and
arbitrary write/move effects on terminal halt edges. PA194QH matches none.
Bit interchange is a deliberately enlarged structural comparison, not a
claim that complementing bits preserves a zero-blank start. Novelty is
limited to the pinned, recognized literal corpus, not arbitrary machines
that an unexecuted parameterized generator could produce.

The provisional QC idea reproduced existing Q exactly. Its duplicate
receipt is retained as a positive control for the comparison procedure.

WHAT IS INCLUDED
================
construction/  Frozen Q grammar/folds, H parent, compiler, and build_qh.py.
machine/       Dense/native tables, resolved source, labels, and certificates.
verification/  Independent source/tape checker, free-term emitter and command
               checker, 61-line K/S exchange certificate, and proof review.
comparison/    Complete delivery ledger, frontier, exact novelty checker,
               broader census, controller matrix, and family analysis.
references/    Retained PA calibration and H-command manuscript dependencies,
               repository proof-status statement, and scoped Lean context.
search/        Bounded unsuccessful reduction searches, code, frozen inputs,
               logs, and endpoints. C++17 is required only to rerun searches.

SEARCH LIMITS
=============
Physical grammar searches used 8,181,452 proposal slots; the best scored
allocation was 194. All 60 retained endpoints were independently checked
to resolve the original 3,673-site instruction graph. This is source binding,
not full physical verification of 60 newly constructed machines.
Logical-head/gate searches used 30,600,000 proposals and did not beat 194.
Some scores are explicitly optimistic; see the search README files.
These searches give no state lower bound, minimality result, or proof that
a smaller machine does not exist.

SOURCE SNAPSHOT AND LICENSES
===========================
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: b5086c8db0f5778b9569c1ce36b7fe0310d5f225
Requested PA and incoming collections were compared at that snapshot.
ZFC and ConciseIPRA were inspected for transferable methods; their machines
are not counted as PA consistency machines. No change was made to the
source repository. Retained notices and imported licenses identify the
authors of the constituent constructions and verification infrastructure.
See NOTICE_parents.txt and the license files in comparison/, verification/,
and search/physical/licenses/.

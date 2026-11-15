PA194ORH RESEARCH PACKAGE — 15 NOVEMBER 2026
==========================================

RESULT
------
No valid machine with fewer than 194 working states was obtained.
The principal new design is PA194ORH: a binary, single-tape, two-way
blank-input Turing machine with 194 working states and a separate halt
label. Its dense table is machines/PA194ORH/machine.tm.

SHA-256:
c16bef7a1587e31adaae747d5bad26721f30bb5c6c33dd4b798be95f5141f1d4

The new operand reassociation changes 134 physical source addresses while
preserving every resolved primitive instruction of PA194AX11H. A separate
history-selector repair preserves a second, hidden use of the routine's
entry control. A tempting 193-state version that omitted this repair is
explicitly rejected in the research artifacts.

The written proof establishes in iPRA exact relative halting/nonhalting
equivalence with the calibrated AX11H parent. Composing with the reviewed
revised AX11H written theorem gives

  iPRA |- Con(PA) <-> not Halt_blank(PA194ORH).

This is a written mathematical proof with executable finite certificates,
not a new completed Lean proof. The absolute PA endpoint uses the exact
mapped current Foundation PA-refutation predicate of the inherited
calibration. The report explains every dependency and the formalization
boundary; finite execution checks alone are not an end-to-end proof.

START HERE
----------
  report/main.pdf                  Complete 26-page report.
  report/main.tex                  Main LaTeX source.
  proof/relative_ORH.tex            Relative iPRA proof and polynomial clocks.
  comparison/calibration_review.txt Independent review of the parent theorem.
  reference/calibration_AX11H.zip   Exact revised parent calibration archive.

The report includes all 388 transitions of PA194ORH. The archive also
contains the parent proof manuscripts, source-code inputs, comparison
ledgers, and a second new 194-state machine PA194OR. The latter applies
the same operand transformation to the original command protocol, with
its separate written relative proof in research/engine/relative_OR.tex.
Its absolute PA calibration is inherited from that primary parent.

EXACT TM CONVENTIONS
-------------------
Each table row is: state read_symbol write_symbol direction next_state.
Directions are L and R, each a one-cell move. Alphabet = {0,1}.
Initial tape = all zero; initial head coordinate = 0; initial state = 0.
Dense working states = 0,...,193. Halt = 194, with no outgoing row.
Native start/boundary/halt labels = 74/84/254. labels.json gives conjugacy.

ACCEPTED DESIGNS
----------------
PA194ORH: 194 controls, 3,671 sites, 4,778 source outcomes,
         57,942-step complete blank startup.
PA194OR:  194 controls, 3,673 sites, 4,780 source outcomes,
         58,170-step complete blank startup.

Both pass independent literal-row symbolic replay for arbitrary natural
primary registers, an arbitrary nonnegative gap, and an arbitrary
nonempty finite spare list. The checker derives four generic list lemmas
from literal rows and uses no construction arithmetic-box oracle.
Both are structurally new against the 520 supplied spanning 194-state
classes, and their broad canonical graph identities differ from each other.

REPRODUCE
---------
From this directory, using Python 3.12 (standard library only):

  python3 -B verify_all.py

This rebuilds both accepted machines in a temporary directory, compares
their exact tables and source artifacts, performs complete independent
literal replays, checks source and relative-clock bindings, checks novelty,
replays the command-word algebra and the expected rejected examples, and
writes verification/release_check.json. It does not invoke Lean.

Optional: regenerate all corpus canonical forms during the novelty checks:

  python3 -B verify_all.py --recompute-novelty

Individual commands:

  python3 -B construction/build.py --output rebuilt/PA194ORH
  python3 -B construction/build_or.py --output rebuilt/PA194OR
  python3 -B verification/check.py rebuilt/PA194ORH rebuilt/PA194OR
  python3 -B proof/relative_ORH_check.py
  python3 -B research/engine/relative_OR_check.py
  python3 -B research/logic/ORH_audit.py
  python3 -B comparison/check_novelty.py machines/PA194ORH/machine.tm

Run without -O, since executable checks use Python assertions.
The finite receipts and the written arithmetic soundness proofs are
complementary. Neither is advertised as a kernel-checked Lean endpoint.

REPORT BUILD
------------
From the package root, with a conventional LaTeX installation:

  python3 -B report/generate_tables.py
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory report report/main.tex

Repeat pdflatex until cross-references settle (normally two or three runs).
The needed packages are named in main.tex. The PDF was rendered and
visually reviewed; verification/pdf_layout_check.json records the result.

COMPARISON
----------
Pinned repository:
  https://github.com/VladimirReshetnikov/ProveIt
  43d9041f5571936c45c583f7f9d7f6eed9e0fd84

The comparison covers 93 filed PA packets and all four current incoming
archives: 97 deliveries, 83 named principal/supplementary designs, and
29 mechanism families. Recognized complete explicit-table data yield 520
spanning 194-state graph classes and two nonspanning diagnostics. These
are NOT 520 proved consistency machines: experiments and rejected inputs
are included. All 54 recognized 193-state graph classes are rejected or
unproved, not accepted smaller answers.

comparison/README.txt documents the census recognition boundary, table
provenance, duplicates/aliases, and exact novelty equivalence. The included
representatives suffice for offline novelty checks. Recreating the full
source census needs a checkout of the pinned upstream revision; it is not
bundled because its several gigabytes are unnecessary for local checking.

RESEARCH STATUS
---------------
research/reader_search/ and expanded_search/ contain reproducible C++17
grammar-search sources and frozen inputs, with honest finite-run receipts.
research/engine/ has physical quotient searches, scanner experiments,
rejected193 counterexamples and the supplementary PA194OR relative proof.
research/logic/ has new MP-protocol algebra, a checked auxiliary195 table,
contraposition searches and exact parameter screens. Its own README gives
the commands and precise scopes.

All directories or files marked REJECTED/rejected contain counterexamples
or failed designs. They are retained as research evidence, not as claimed
consistency machines. Search scores are not proof certificates, and none
of the negative searches proves a general 194-state lower bound.

ATTRIBUTION AND INTEGRITY
-------------------------
Imported numerical calculus, compiler/runtime infrastructure, parent
calibration and corpus metadata are attributed in PROVENANCE.json,
reference/, comparison/, and the research READMEs. Retained licenses are
under licenses/. The new main contribution is the repaired operand
reassociation and its verified arithmetic relation to the calibrated
parent, alongside the comparison and additional research.

SHA256SUMS binds the release contents, except itself. Re-running a checker
may update receipt paths or elapsed times; that changes those receipt
bytes without changing the fixed machine identities printed above.

A 468-BYTE CHECKED PRESENTATION OF iPRA
Prepared for Vladimir Reshetnikov, November 12, 2026

RESULT AND LIMIT
The complete direct-source checker has 271 significant Python tokens,
305 AST nodes, and 468 normalized UTF-8 bytes. Its exact matched control
has 272 / 306 / 469. The audited current coordinate records, including
19 incoming archives, are 241 / 262 / 469 in different programs.
The new checker lowers the byte record to 468. It does not lower the
independent token or AST record, and it does not remove an arithmetic
axiom or establish an absolute minimum. The requested mathematical
breakthrough was not obtained. This is a verified partial research result.

START HERE
  ipra_468_report.pdf   compiled report, including explicit rules and
                        the interpretation argument
  ipra_468_report.tex   complete standalone report source
  CLAIMS.json          precise claims and limitations
  code/checker468.py   complete measured checker
  code/readable_checker.py   readable standalone expansion

The construction composes the existing shared computation/hypothesis
leaf with the existing even-offset syntax encoding. Their composition
is not present among the audited small direct-source checkers.
It preserves the canonical public theory and its inherited whole-domain,
actual-equality bi-interpretation with full first-order intuitionistic
primitive recursive arithmetic. Both comparison graphs are x=y.

INPUT CONTRACT
The compact checker consumes one JSON array from right to left. Its last
element is [goal, 0], where goal is a canonical closed guarded Eq/D
formula. Every preceding consumed packet has four fields [m,s,u,t].
Data are finite exact-integer/list trees. The public syntax and alphabet
are promises of this compact interface, not separately validated by
the 468-byte checker. An unused prefix is allowed. Success is normal
exit with exactly ACCEPT followed by a newline. Exceptions reject.
Ideal finite execution ignores a physical machine's resource ceiling.

REPRODUCE
Use CPython 3.12.14 for the exact source measurements:
  python3 reproduce.py

The archive carries 108 isolated regression checks, including optimized
Python execution, noncanonical auxiliary data, scope rejection, and
false-goal mutations. These tests support the written semantic proof;
they are not a formal proof of arbitrary-certificate soundness.
An additional eight-run suite verifies two explicit false-public-goal
attacks against the correct checker and deliberately weakened controls.
The readable standalone expansion also passes its 28 included fixture checks.

Example (a zero-iterator computation):
  python3 code/checker468.py < code/fixtures468/computation_zero.json

BUILD THE REPORT
  pdflatex -interaction=nonstopmode -halt-on-error ipra_468_report.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_468_report.tex

PROVENANCE
Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 78edba03ee060644464f76e388578584b356520a
Subtree: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Exact controls, inherited proof sources, source hashes, census, and
test results are included. The inherited Lean source excerpts identify
existing theorems; this work did not build Lean or formally verify the
new Python codec. No repository publication or modification was made.

Reference sources retain the upstream MIT No Attribution license,
included at reference/LICENSE-upstream.txt.

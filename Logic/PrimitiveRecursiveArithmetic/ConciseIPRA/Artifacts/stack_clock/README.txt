CHECKING iPRA WITH A STACK CLOCK
13 November 2026

READ report.pdf FIRST (editable source: report.tex).

RESULT AND LIMIT
The requested construction below the current complexity frontier was not
obtained. The complete new checker is 327 significant Python tokens,
378 AST nodes, and 611 normalized UTF-8 bytes. Its exact matched control
is 309 / 355 / 582. The new program is larger on all three coordinates.
It does not beat the exact envelope 303 / 338 / 582, and does not beat
the smaller compact presentations. No absolute minimality, arithmetic
axiom deletion, or new Lean/Rocq verification of Python is claimed.

WHAT IS ESTABLISHED
The interpreter does not need a separately advanced fresh-name counter.
Let P be the unread packet list and N its length after removing the goal.
The current scope is exactly len(P)-N. Scan a goal before popping its
packet. Then the pop itself makes the derived scope decrease by one.
A written simulation proves that the new checker accepts exactly the
same finite JSON certificates as the retained-validation control, with
unchanged public conclusions. No certificate translation is required.

The mathematical theory remains the full native scalar iPRA presentation.
The report states its eight primitive axiom/rule families, ordinary
intuitionistic realization, logical macros, and inherited bi-interpretation.
Both numerical domains are whole, equality is actual, and both numerical
comparison graphs are x=y. The source of those imported theorems is explicit.

INPUT AND SUCCESS
Input is a whole JSON array, with a closed actual-binding Eq/D goal last.
Earlier records [source,target,template,major] are popped right to left.
Every proof call consumes one record. Unused prefix data are permitted.
Zero is encoded by 1; true is an allowed spelling alias; genuine bound
variables have codes 3,5,7,... . Public false, floats and padding slots
are rejected. Acceptance is zero exit status and exactly ACCEPT plus LF.
Ordinary and optimized (-O) Python retain all checks.
Mathematical completeness uses ideal unbounded finite resources.

RUN
  python3 code/checker.py < examples/zero_computation.json
  python3 code/checker.py < examples/induction.json
  python3 code/checker.py < examples/capture_four.json
  python3 reproduce.py
  python3 reproduce.py --metrics-only
  python3 build_report.py

The first two proofs accept; the capture attack rejects with an exception.
The reproduction requires only Python's standard library and no network.
The PDF build requires an installed TeX distribution with the packages in
report.tex. Use CPython 3.12.14 for the exact source-size convention.

CONTENTS
  report.tex / report.pdf       Complete mathematical report.
  code/checker.py               Complete measured standalone checker.
  code/checker_readable.py      Standalone explanatory companion.
  proofs/                      Universal simulation and implementation note.
  examples/                    Directly runnable proofs and rejections.
  fixtures/                    All fourteen inherited native proof fixtures.
  reference/                   Exact controls, source chapters, Lean
                               identification module, license, provenance.
  evidence/                    Metrics, final verification and independent review.
  verify.py / reproduce.py      Offline verification and measurement.
  build_report.py              Local two-pass PDF compilation.
  CLAIMS.json                  Machine-readable claim boundaries.
  PROVENANCE.json              Pinned repository and archive identities.
  MANIFEST.sha256              Integrity hashes (excluding the manifest itself).

The reference Lean module depends on the upstream repository. It is not
a self-contained Lean project or a verification of the Python checker.
The reference chapter files are source parts of the upstream book, not
standalone TeX documents; compile report.tex at the archive root.

VALIDATION
The final code was checked in 6,913 run comparisons, 6,554 independent
grammar comparisons, 17,280 opener comparisons, 4,704 false-export
mutations, and 408 isolated normal/-O command-line executions, with zero
failures. A corrected capture fixture is accepted by a deliberately
scope-weakened mutant and rejected by the delivered checker. Finite tests
support the written universal argument; they do not replace it.

SOURCE PIN
  VladimirReshetnikov/ProveIt
  65c32fbe4730bfe5a064502b0b95ebc798c732fa
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All four incoming ZIPs at this snapshot were inspected. No remote
repository content was changed. The remaining-length construction answers
a protocol question in the certificate chapter, not the stronger requested
size crossing. The distinction is deliberate throughout the deliverable.

CLOSING UPSTREAM CHECK
  6ce5acc401f0c84be90dc5c38dc1487e391122c6
The closing snapshot integrates the four reports and adds the seven-rule
reconstructed-introduction presentation. Its reported exact checker is
313/357/590 and its larger synthesis reference is 1896/2182/7639. Neither
changes the exact minima above. The new package is upstream work, not a
contribution of this report. Its status and README are included in evidence/.

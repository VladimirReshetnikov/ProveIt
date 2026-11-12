CONCISE iPRA: SCOPE REUSE AND MATHEMATICAL LIMITS
Prepared for Vladimir Reshetnikov, November 11, 2026.

RESULT
The same fully validated Eq/Q/D presentation now has a complete standalone
checker of 881 normalized bytes / 393 significant tokens / 460 AST nodes /
500 gzip-9 bytes, against the exact incoming 897 / 401 / 468 / 505 control.
The Eq/D public variant is 862 / 382 / 446 / 493, against 878 / 390 / 454 /498.
The gzip figures are informational only.

This is a modest implementation improvement, not a newly simpler axiom basis.
No absolute minimum or mathematical breakthrough is claimed. In particular,
the separate compact guarded 520-byte profile has a different input contract.

The changes reuse the proof kernel's first scope traversal and unpack the
JSON input directly into prefix and conclusion. Exact integer/list validation
of the entire certificate, including unused prefixes, is retained. The report
proves equality of successful input sets with the frozen controls, abstracting
from physical resource limits. The mathematical calculus and both inherited
iPRA interpretation round trips are unchanged.

MATHEMATICAL RESEARCH RESULTS
1. A coordinatewise model on N x N validates all contextual equation induction
   instances but refutes coverage. A closed Q/Q/Q equation formula separates
   the original case introduction from a direct-target replacement.
2. A scalar iteration-uniqueness rule implies induction for zero equations and
   for predicates admitting term-defined split retractions. Equality reflection
   needed for a complete replacement of scalar equation induction is unfinished.
   The report marks this gap explicitly; no completed UR-based bi-interpretation
   or smaller UR checker is claimed.

START HERE
report.pdf                          Main compiled report (18 pages).
report.tex                          Main LaTeX source.
sections/*.tex                      Mathematical supplemental sections.
code/checker_full.py                 Primary complete full Eq/Q/D checker.
code/checker_eqd.py                  Eq/D public-language checker.
code/checker_readable.py             Annotated standalone full checker.
reference/validated_core/code/       Exact matched incoming controls.
reference/validated_core/tests/      Inherited fixtures and profile manifest.
reference/mathematics/               Attributed inherited mathematical proofs
                                    and the complete sorted arity decoder.
reference/*.lean                    Selected source snapshots; not a complete
                                    standalone Lean project.
evidence/metrics.json                Whole-module metrics and source hashes.
evidence/validation.json             Full executed verification receipt.
evidence/*.normalized.gz             Deterministic gzip-9 normalized programs.
PROVENANCE.json                      Exact repository snapshot and source IDs.
CLAIMS.json                         Machine-readable claim boundaries.
SHA256SUMS                          Final payload hashes.

RUN
    python3 code/checker_full.py < examples/computation.json
    python3 -O code/checker_full.py < examples/computation.json
Both print exactly ACCEPT and exit normally. Every exception rejects.
The only imported checker dependency is the Python standard JSON library.

REPRODUCE
    python3 reproduce.py
    python3 build_report.py
The first command is offline and uses only the standard library. It regenerates
metrics, deterministic gzip files, and verification receipts. The frozen runtime
was CPython 3.12.14. The document build needs pdflatex and its listed packages.

Executed verification: 13,019 scope-preflight comparisons per interface;
606 complete checker processes including normal and optimized Python;
zero discrepancies. Finite testing supports the written preservation proof.
No new Lean/Python correspondence theorem or local Lean rebuild is claimed.

SOURCE SNAPSHOT
VladimirReshetnikov/ProveIt, commit
56249a4263cae9aad9ba87d23d0ee6d4ff6483bc
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
All three incoming ZIP archives at that snapshot were inspected.
Inherited ProveIt material is under the included MIT No Attribution license.

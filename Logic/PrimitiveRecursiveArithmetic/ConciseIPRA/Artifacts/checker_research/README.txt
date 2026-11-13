CONCISE iPRA: AN AUDITED FRONTIER AND AN EXACT 576-BYTE CHECKER
13 November 2026

RESULT STATUS
The requested globally smaller axiomatization has not been obtained.
This is a limited implementation refinement of an existing exact-binding
presentation, with the same input language and same acceptance semantics.

                    tokens    AST nodes    normalized UTF-8 bytes
Matched control       309        355                 582
New checker           310        358                 576

The six-byte saving worsens the other two coordinates. It is not a new
arithmetic axiom basis, a Pareto improvement, or a global size record.
The compact seeded-sequent envelope is 238/255/455 across different
programs. The exact-binding envelope is 303/338/576 with this refinement,
also across different programs. No single program attains either triple.

CONTENTS
ipra_checker_research.pdf  Compiled report with exact scope and proof.
ipra_checker_research.tex  Self-contained LaTeX source of that report.
code/checker.py            Complete measured refined checker.
controls/                 Frozen matched and frontier sources.
measure.py                Reproduce whole-module size measurements.
tests/verify.py            Exact AST-change check and regression harness.
tests/fixtures/           Included derivations and scope attacks.
evidence/                 Source hashes, measurements, test results,
                          independent review, and bounded novelty audit.
formal/                   Unmodified upstream reference Lean module;
                          not a new independent formal verification.
STATUS.json               Machine-readable claims and limitations.
UPSTREAM-LICENSE.txt      MIT-0 license for copied upstream material.
MANIFEST.sha256            SHA-256 checksums of the archive contents.

REPRODUCE
Run from this extracted directory using CPython 3.12.14:

    python3 measure.py
    python3 tests/verify.py

The test harness compares the actual candidate and frozen control. It
does not fetch network content. It checks 76 certificate cases and 32
full CLI executions, including normal and optimized Python. The written
proof covers the one-expression rewrite; finite tests do not prove the
complete inherited iPRA correctness argument.

To compile the PDF with a normal TeX installation:

    pdflatex -interaction=nonstopmode -halt-on-error ipra_checker_research.tex
    pdflatex -interaction=nonstopmode -halt-on-error ipra_checker_research.tex

CHECKER INTERFACE
The whole standard input is one JSON array. Its final entry is the
public formula, and earlier entries are four-field packets consumed
from the end. Successful verification prints ACCEPT. Errors reject.
Unused prefix entries are permitted. Public statements have actual
binding slots; scalar 1 and Boolean true are public aliases of zero.
The inherited treatment of proof payloads and scope is documented in
the report. Completeness uses the usual unbounded finite resource model.

MATHEMATICAL DEPENDENCIES
The report gives the explicit native calculus and the full first-order
interpretation statements. The substantive arithmetic bootstrap and
upstream checker's correctness argument are identified as inherited.
The refinement is proved to accept exactly the same inputs as its
matched control. It has not been verified in Lean or Rocq.

SOURCE SNAPSHOT
VladimirReshetnikov/ProveIt
65c32fbe4730bfe5a064502b0b95ebc798c732fa
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All four incoming archives at that revision were included in the audit.
The report contains clickable pinned source references. The baseline
receipt records verified Git blob hashes and SHA-256 hashes. The audit
does not claim a proof of an absolute minimum or of global novelty.

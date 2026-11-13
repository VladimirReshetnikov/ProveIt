IPRA: CHECKED PRESENTATION REFINEMENT AND FRONTIER AUDIT
Research deliverable for Vladimir Reshetnikov, November 12, 2026

Read report.pdf for the result, proofs, precise qualifications, and the
induction-free standard-numeral rigidity theorem. report.tex is its complete
LaTeX source; the included result supplement and rigidity fragment are inputs.

STATUS

This package does not establish the absolute simplest axiomatization and does
not beat the compact direct-source envelope 242 tokens / 262 AST nodes /
469 normalized bytes. Those coordinates belong to three different programs.

It refines the stronger whole-input-validated native interface. The mathematical
axiomatization is inherited; the implementation refinements and the auxiliary
rigidity dependency result are distinguished in report.pdf and CLAIMS.json.
The new universal proofs are written mathematics, not a newly completed
Lean/Rocq verification of Python or of the rigidity theorem.

The repository is frozen at:
a0687e8082b7354005d91b0ee105b4fd5ec8cf40
https://github.com/VladimirReshetnikov/ProveIt/tree/a0687e8082b7354005d91b0ee105b4fd5ec8cf40/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

LAYOUT

report.pdf, report.tex        Report and its LaTeX source.
code/                        Released standalone checkers and verification tools.
controls/                    Exact pinned comparison programs; packed wrappers
                             are a separate accounting category, not the claim.
fixtures/                    Certificate inputs and their expected results.
evidence/                    Measurements, full census, hashes and test receipts.
reference/                   Inherited mathematical source fragments, the new
                             rigidity appendix, and the inherited license.
experiments/                  Notes on unsuccessful reductions; no claimed checker.

RUNNING

Use CPython 3.12.14 to reproduce the published normalization metrics.
Each released checker reads one JSON array on standard input. Normal success
prints exactly ACCEPT. Exceptions reject. An unused integer/list prefix is
permitted. See code/FORMAT.txt for the exact input and converter contracts.

After extracting the ZIP, run from this directory:

  python3 code/verify.py
  python3 code/measure.py code/strict_tokens.py code/strict_ast.py code/strict_bytes.py
  python3 code/verify_selfseed_tables.py

The first command validates fixtures and reproduces the module metrics;
the second measures the complete acceptance programs without importing them;
the third checks the finite term-table construction in the rigidity appendix.
None requires network access. The test receipts included in evidence/ describe
exactly what was run. Finite tests are not a proof of universal soundness.

To repeat the much larger frozen repository census, supply an existing checkout:

  python3 code/census.py /path/to/ProveIt/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA --output census.json

The scanner reads sources as data and does not execute them. It is a source
census, not an automatic certification of every program found in the corpus.

PDF BUILD

On a normal TeX Live installation with the packages listed in report.tex:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

Inherited reference/*.tex chapters are source excerpts with their original
article macros. They are reference material, not separate compilable documents.
The included report is self-contained as a LaTeX build.

SCOPE OF REPRODUCTION

Python's finite recursion, memory, and integer parsing limits can reject very
large valid finite certificates. The mathematical checker is understood with
the usual unbounded-resource recursive-algorithm semantics, as are the pinned
controls. No finite hardware limit is an additional axiom of iPRA.

The proof-stream converter is deliberately partial where specified in
code/FORMAT.txt. It is untrusted producer code. Acceptance of its output is
always determined afresh by the standalone checker; the mathematical
completeness argument does not assert that this helper implements every
possible proof translation.

PROVENANCE

The exact inherited controls and source chapters are covered by the MIT No
Attribution license in reference/LICENSE.txt. The pinned commit, archive hashes,
source paths, and checksums are recorded in evidence/frontier_summary.json and
MANIFEST.sha256. No GitHub mutation or publication was performed.

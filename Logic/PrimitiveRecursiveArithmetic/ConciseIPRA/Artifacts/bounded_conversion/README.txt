BOUNDED LOCAL CONVERSION FOR iPRA
Research package, 12 November 2026

STATUS
This package gives a new seven-rule raw-term presentation equivalent on all
open sequents to the native scalar core. It does NOT establish a presentation
below the repository's smallest complete-checker frontier. It is a partial
research result, not a solution of the requested global size target.

The report contains the complete rule inventory, the bounded conversion
construction, an explicit equality-transport derivation, the bi-interpretation
dependency, measurements, verification results, and further research questions.

FILES
  ipra_bounded_conversion.tex  Standalone LaTeX report source.
  ipra_bounded_conversion.pdf  Compiled report.
  code/checker.py             Standalone checker for the new raw calculus.
  code/control.py             Pinned weak-head-normalizing comparison checker.
  code/verify.py              Reproducible size and certificate checks.
  evidence/                  Measurements, test results, source provenance.
  reference/                 Attributed supporting material and exact controls.

RUN
  Reference environment: CPython 3.12.14 (exact ast.unparse measurements).
  Python 3.10 or later is required by the checker's match syntax.
  python3 reproduce.py
  pdflatex -interaction=nonstopmode -halt-on-error ipra_bounded_conversion.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_bounded_conversion.tex

The new equivalence is a written mathematical proof, not a newly compiled
Lean or Rocq formalization. Finite tests verify examples and implementation
boundaries; they do not prove the universal equivalence theorem.

All repository comparisons are pinned to
2fa4637b3bf922beea0052a5210c22b14482950b in VladimirReshetnikov/ProveIt.
All seven incoming archives present at that snapshot were inspected.
No remote repository was modified.

ADDITIONAL MATHEMATICAL RESULT
The ideal bounded-conversion verifier has a primitive-recursive proof
predicate. The particular inherited weak-head verifier does not on its
open-sequent interface. The report proves this with a fixed one-QE
certificate skeleton and diagonalization. This is not a source-size
record; conventional raw iPRA proof verification was already PR.

REFERENCE SOURCES
reference/lean contains exact endpoint files, not their complete
dependency closure or a newly built formalization. Consult the pinned
repository to build the inherited Lean development.

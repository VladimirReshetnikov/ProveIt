# Bounded reflection and guarded witness compilation for iPRA

A 2026-11-16 research package based on the ProveIt iPRA README,
UNIFICATION-PLAN, Bridge README, Derivations README and Core/Search.lean.

* `paper.tex`, `paper.pdf`: mathematical arguments and implementation design.
* `LeanOutline.lean`: explicitly uncompiled Lean formalization specification.
* `finite_reflection.py`: executable bounded-search regression tests, not a proof checker.

## Verification status

The mathematical arguments have been written out, and the Python tests run.
No new Lean kernel-checked iPRA derivations are claimed. In particular the
bounded-formula compiler, binder substitution proof and generic open-sequent
transport remain implementation tasks. No unbounded or uniform evaluator
for arbitrary primitive-recursive code is claimed.

To run: `python3 finite_reflection.py`.
To compile: `pdflatex paper.tex` twice (TeX Live).

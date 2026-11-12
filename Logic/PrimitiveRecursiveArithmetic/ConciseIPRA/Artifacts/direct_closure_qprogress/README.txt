DIRECT CLOSURE INDUCTION FOR iPRA
2026-11-10

STATUS
This package establishes an equivalent primitive presentation of the current
ConciseIPRA calculus. Equation induction no longer carries an existential
witness. It does NOT establish a smaller complete proof checker than the
current 529-byte profile: the included alternatives measure 552 and 568 bytes.
Accordingly it is not a claimed solution of the minimum-checker-size target.

READ FIRST
report.pdf is the complete paper; report.tex is its editable LaTeX source.
The paper gives every primitive axiom and rule, both proof transformations,
the full-iPRA interpretation argument, measured comparisons, and further
research questions. There is no claim of absolute minimality or new arithmetic
strength. NPrf.qIProg is already a derived theorem in the pinned development.

REPRODUCE
  python3 reproduce.py
  pdflatex -halt-on-error report.tex
  pdflatex -halt-on-error report.tex

Python uses only the standard library. CPython 3.12 is the comparison runtime.
Actual source checks and process tests run without the repository or network.
The compact checkers read JSON from standard input; acceptance is exit code 0
and stdout exactly ACCEPT followed by a newline. Exceptions reject.

CONTENTS
  compact/       Standalone complete compact checkers, fixed JSON fixtures,
                 a process-test runner, reproducible metrics, and their README.
  audit/         Independent readable named-syntax checker, both proof
                 transformations, example proof trees, and audit results.
  theory/        Two independent written derivations of the equivalence.
  reference/     Attributed, frozen upstream mathematics and Lean sources;
                 provenance.json pins the exact commit and file checksums.
  CLAIMS.json    Exact positive claims and explicit nonclaims.

The frozen Lean development is background evidence, not a Lean verification
of the new primitive presentation. It was not built in this environment.
reference/lean/lakefile.toml is a convenience standalone project configuration.
The upstream Lean source files are unchanged. Building them needs Lean 4.32.0
and the matching mathlib version. No new Lean verification is claimed.

COMPARISON POINT
VladimirReshetnikov/ProveIt
8662bc0a00f4e77e482f7d141d7a4f919f70f9aa
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The baseline sources and their original mathematical contributions are
attributed in the paper. Their MIT-0 license is retained in reference/.

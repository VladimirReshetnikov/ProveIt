Report208  First maximum frequencies in ordered partitions
4 October 2026

A386374 (weak first maximum) and A386375 (strict first maximum).
The PDF contains complete mathematical statements, proofs, scope and references.
The real inverse theorem is for the weak sequence.

CONTENTS
Report208.tex and Report208.pdf: editable source and report.
verify.py: exact recurrences, composition/set-partition checks, symbolic identities,
  and 100-digit floating-point diagnostics.
independent_check.py: direct word enumeration, independent rational EGF extraction,
  rational constant checks and correction identities through order four.
reproduce.py: executes checks, generates all data and tables, compiles the PDF,
  and creates a deterministic ZIP of actual rebuilt deliverables.
data/: canonical complete finite-check output and diagnostic values.
tables/: all three report tables, generated from data by reproduce.py.
SOURCES.txt: public references and reading limits. No third-party full texts included.
requirements.txt: Python package versions used for the supplied results.

REPRODUCTION
Requires Python 3.11+ and pdflatex with the packages named in Report208.tex.
The tested environment used Python 3.12.14, mpmath 1.3.0, sympy 1.14.0 and
pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian).
Install requirements if needed using your normal package-management procedure.
From this directory run:
  python3 reproduce.py --out /tmp/report208-normal
  python3 -O reproduce.py --out /tmp/report208-optimized
Then compare the two Report208-reproducibility.zip files byte-for-byte.
The output directory must be outside the extracted source directory.
Do not use --initialize during validation; it is only an authoring switch that
permits missing baseline generated files. Existing baselines are always checked.

To test explicit failure behavior (must exit nonzero):
  python3 reproduce.py --out /tmp/report208-failure --self-test-failure
  python3 -O reproduce.py --out /tmp/report208-failure-O --self-test-failure
No output files are written by these deliberately failing commands.
All guards use exceptions, not assert statements disabled by -O.

The generated canonical independent data omits only the raw checker's
optimization flag. Raw checker logs therefore need not match across modes.
With matching Python/package and LaTeX versions, actual archive members and
whole ZIP bytes match in normal and optimized runs. Cross-toolchain PDF byte
identity is not promised. ZIP metadata, member order and stored compression
are fixed. Rebuilding never downloads sources or calls an external service.

INTERPRETATION AND LIMITS
The diagnostics use finite positive-pole sums, not interval arithmetic.
The error table uses the fixed range 2..60 for both exact-pole and root-free
sums, rather than the theorem's moving finite window. Exact m=1 contributions
are added separately for the recorded small-n absolute coefficient residuals.
Phase diagnostics use real n, not rounded integers, and a fixed range 2..m+30.
Finite checks do not certify infinite asymptotic theorems. Those are proved
in the PDF. Numerical inverse constants/onset and positive-root intervals are
not certified. Exact recurrence or certified neighboring evaluations resolve
integer-rounding ambiguity. No worldwide originality claim is made.

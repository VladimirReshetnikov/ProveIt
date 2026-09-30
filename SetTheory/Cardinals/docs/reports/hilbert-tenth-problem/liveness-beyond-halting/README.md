# Beyond Halting
## A Progress-Modulus Hierarchy for Diophantine Liveness

Research manuscript and exact finite-certificate implementation, September 30, 2026.
Prepared for the ProveIt research program.

## Read the article

`beyond_halting.pdf` is the rendered article. `beyond_halting.tex` is its complete,
editable LaTeX source with an inline bibliography. The article includes twelve
specific further research questions and a proposed Lean integration plan.

The central result is the equivalence, for a computable binary-controlled system:

- some recurrent run meets a computable deadline;
- the accepting schedules contain a nonempty effectively closed subclass;
- some accepting schedule has hyperimmune-free Turing degree.

A second explicit construction realizes every computably enumerable Turing degree
as the exact least oracle degree capable of computing a successful deadline.
The article also proves the sharp progress hierarchy, gives a step-exact rational
piecewise-affine realization, and constructs a finite-horizon quartic compiler.

## Reproduce the computation

Python 3.10 or newer, standard library only:

```sh
python3 code/test_clock_compiler.py
python3 code/clock_compiler.py
```

The first command writes `artifacts/test_report.json`. The second writes
`artifacts/example_certificate.json`, containing a complete 52-variable,
137-residual example, its rule-labelled trace, and its unique natural witness.
All polynomial and rational computations are exact. No external solver is used.

The recorded run used Python 3.13.5. It checked, among other families, 3,906 rule
sequences, 3,888 local candidate assignments, 3,150 guard/update cases, and 496
single-coordinate increments of valid witnesses. All passed. The report's
17,197 total combines assertions and enumerated assignments; it is not a count
of independent infinite-system proofs.

## Build the PDF

Use a TeX Live installation with pdfLaTeX, AMS mathematics, New PX, Microtype,
TikZ, tcolorbox, enumitem, listings, fancyhdr, hyperref, and cleveref:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error beyond_halting.tex
```

Alternatively run `pdflatex -interaction=nonstopmode -halt-on-error
beyond_halting.tex` three times. No BibTeX or Biber pass is needed. Font files
are not included in this package; install the appropriate standard TeX packages.

## Scope and proof status

The manuscript contains conventional mathematical proofs, with classical
ingredients attributed. The HIF and low basis theorems, MRDP, and classical
analytical recurrence hardness are not claimed as new. The integrated
clock/degree framework, c.e.-degree realization, exact compiler, and applications
are developed in the manuscript; independent verification and priority review
remain appropriate. No longstanding named conjecture is claimed to be solved.

The Python module implements only a finite-horizon compiler. Its number of
variables grows with the horizon. Unique witnesses for a fixed rule-labelled
trace do not imply fixed-arity single-fold or finite-fold MRDP representations.
The program does not implement a general MRDP extractor, an explicit small
universal-machine table, a quartic solver, or a decision procedure for infinite
recurrence.

No new Lean formalization is included, and the repository was not rebuilt.
Public MRDP source was inspected at commit
`b6bf6406a4c49017fedc6fba068b36c634987150`; documentation was also inspected at
`b998f70c6886e6a00339a6f4a02ed8625324d357`. The source ledger records provenance.

The geometric construction uses exact guarded rational affine dynamics. It is
not claimed continuous, robust to noise, or physically implementable at infinite
precision. The autonomous-map analytical result explicitly quantifies over an
arbitrary real scheduler parameter; it does not extract noncomputable information
from a finite rational input.

## Files

- `beyond_halting.tex`, `beyond_halting.pdf`: article source and rendered article.
- `code/clock_compiler.py`: exact polynomial and two-stack certificate code.
- `code/test_clock_compiler.py`: finite tests.
- `artifacts/example_certificate.json`: complete worked example.
- `artifacts/test_report.json`: executed test results.
- `research/source_ledger.md`: sources and inspection scope.
- `SHA256SUMS`: checksums for the delivered content, excluding the checksum file.

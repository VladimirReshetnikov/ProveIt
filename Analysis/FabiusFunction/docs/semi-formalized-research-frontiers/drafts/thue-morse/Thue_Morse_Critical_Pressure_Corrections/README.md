# Beyond the Square-Root Cusp

**Logarithmic critical corrections and equilibrium selection for digital-product pressure**

Research draft prepared with ChatGPT for Vladimir Reshetnikov, 29 September 2026.

## Main results

For every integer base `b >= 2`, let `delta = |c|` and
`kappa_b = sqrt(2 (b-1) log b)`. For every `0 < eta < 1/2`, the article proves

```text
P_{b,1}(c) = kappa_b sqrt(delta)
           - (b-1) delta log(1/delta)
           + [b log b + (b-1)(EulerGamma - 1)] delta
           + O(delta^(3/2 - eta)).
```

It also proves that the equilibrium probabilities at small nonzero critical
phases converge weakly to half the point mass at zero plus half normalized
Lebesgue measure. In the bounded-detuning window `s = 1 + u sqrt(delta)`, the
selected atomic weight is

```text
w_b(u) = (1 + u log b / sqrt(u^2 (log b)^2 + 8 (b-1) log b)) / 2.
```

The normalized eigenvectors, a right-eigenfunction boundary layer, and the exact
leading finite-product amplitude are also obtained. Nine further research
questions are included.

## What is new relative to the inspected repository

The predecessor `Thue_Morse_Critical_Pressure` already proves the leading
square root, the atomic Jordan block, and the leading bounded-detuning
crossover. This article credits those results and reconstructs the necessary
foundation. Its targets are the predecessor's explicit questions “The next
critical term” and “Eigenfunctions, eigenmeasures, and equilibrium measures.”
The latter is answered for weak selection and the first right boundary layer;
a full description of the left boundary layer remains open here.

Snapshot inspected: `1085b506d65e207a05b7e9c861bb1fe88432fe38`.
No source repository files were modified.

## Contents

- `article.pdf`: the 21-page article.
- `article.tex`: editable LaTeX source with embedded bibliography; keep `data/`
  beside it for the two numerical tables used by the source.
- `code/verify.py`, `data/verification.json`, and `data/run.log`: executable
  diagnostics and the recorded run, including library versions and residuals.
- `data/pressure_table.tex`, `data/selection_table.tex`: generated tables.
- `CLAIMS_AND_VALIDATION.md`, `source_manifest.json`, and
  `data/build_validation.json`: scope, sources, and build audit.
- `requirements.txt`, `Makefile`: reproduction instructions/dependencies.

## Build the PDF

A TeX installation needs pdfLaTeX, Libertinus, AMS packages, microtype,
booktabs, aliascnt, cleveref, xurl, and the other packages named in the preamble.
No custom font files are distributed.

```sh
make pdf
```

Equivalently, run the following command three times from this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

No BibTeX step is needed. The PDF is directly readable without installing any
software beyond a PDF reader.

## Reproduce the diagnostics

```sh
python -m pip install -r requirements.txt
OPENBLAS_NUM_THREADS=1 python code/verify.py
```

The environment-variable syntax is for POSIX shells. On Windows, set the
variable using the shell's syntax or omit it. The script accepts
`--identities-only` to skip the larger collocation runs and `--output-dir`
to preserve the shipped data:

```sh
python code/verify.py --identities-only --output-dir fresh_checks
```

The largest matrix uses 2,097,152 mesh points. Sparse eigenvalue routines can
require several hundred megabytes of memory. The script uses no network
access. `make clean` removes TeX intermediates but retains the PDF and data.

## Status and limits

The article contains ordinary mathematical proofs. It is not independently
refereed, Lean/Rocq verified, or accompanied by rigorous interval spectral
enclosures. The computational outputs are diagnostics and are not premises
of the analytic proofs. A bounded literature/repository search is not an
unrestricted guarantee of novelty. No complete transseries, global phase
classification, or uniform growing-detuning theorem is claimed.

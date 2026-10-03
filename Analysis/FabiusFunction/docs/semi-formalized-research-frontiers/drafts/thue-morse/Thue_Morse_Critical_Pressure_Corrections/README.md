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
OPENBLAS_NUM_THREADS=1 uv run --no-project --with numpy==2.3.5 --with scipy==1.17.0 --with mpmath==1.3.0 python code/verify.py
```

The environment-variable syntax is for POSIX shells. On Windows, set the
variable using the shell's syntax or omit it. The script accepts
`--identities-only` to skip the larger collocation runs and `--output-dir`
to choose the output directory (default `recomputed/`; the shipped `data/` is
overwritten only by `--output-dir data`):

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

## Editorial amendments (ProveIt, 2026-09-29)

Made in the editorial pass after batch 57 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-29)`, every change to the program `ed. (2026-09-29)`.
The byline "prepared with ChatGPT" is kept as delivered.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-29)" is defined in the preamble. A note after Corollary 7.1 records
  that its amplitude asymptotic is not new: the predecessor
  `../Thue_Morse_Critical_Pressure/` already states
  `int_0^1 P_pm(c)1 dx ~ pm a_b/(pi^2 kappa_b sqrt|c|)`, `a_b = 2 log b`
  (its `eq:critical-amplitudes`), and `A_b(c)` here is exactly
  `int_0^1 P_+(c)1 dx`; the new part is the derivation from the normalized
  eigenvectors. This scope note also covers the abstract, the claims table
  of Section 1, "Main results" above ("the exact leading finite-product
  amplitude") and the row "Exact leading amplitude constant" of
  `CLAIMS_AND_VALIDATION.md`. The paragraph "How to reproduce the package"
  gives the new default output directory, with its double hyphens set so
  that they no longer print as en dashes.
- Reciprocal notes now stand under the questions "The next critical term"
  and "Eigenfunctions, eigenmeasures, and equilibrium measures" of
  `../Thue_Morse_Critical_Pressure/article.tex`.
- Notation differs from the predecessor's: `ell` here is evaluation at 0
  (the predecessor's `ell_0`); the predecessor's `ell` is
  `Xi + 2 log(2/pi) ell_0`; `G` here is the predecessor's
  `G + 2 log(2/pi) H` (disclosed in Section 3); `a` is its `a_b`.
- `article.pdf`: rebuilt with `latexmk -pdf -interaction=nonstopmode
  -halt-on-error article.tex` (MiKTeX 26.2 pdfTeX 1.40.29): 21 pages, as delivered,
  746,290 bytes; no error, undefined reference, duplicate destination
  or overfull box; no Type 3 font. The pages carrying the changes were
  rendered and inspected.
- `data/build_validation.json`: a build record, filed as data. Its `pdf`
  entries `bytes` and `sha256` were recomputed for the rebuilt PDF and a key
  `editorial_amendment` says so; its other fields describe the delivered
  build.
- `code/verify.py`: the default `--output-dir` is now `recomputed/` instead
  of the recorded `data/` (which holds the receipt and the two tables the
  article inputs), so a plain run and `make verify` no longer overwrite
  them; all outputs are written with LF line endings on Windows too. A full
  rerun of the amended program on a copy (2026-09-29, `uv run --no-project
  --python 3.13.5 --with numpy==2.3.5 --with scipy==1.17.0
  --with mpmath==1.3.0 python code/verify.py`, 32 s) reproduced
  `data/pressure_table.tex` and `data/selection_table.tex` byte for byte and
  `data/verification.json` to eigensolver noise (pressures within 1e-10
  relative; residual fields, which are at or below 1e-11, and
  `elapsed_seconds` vary).
- The collocation mesh does not place nodes at the kinks `b^n c mod 1` of
  the eigenfunction. A kink-resolving mesh (an independent check at filing) moves the
  tabulated pressures by 1e-9 to 3e-8 and brings the fitted linear
  coefficient within about 0.5% of `B_b`; the tables are diagnostics.
- `data/run.log` is the packager's console capture and carries the
  packager's sandbox path; it is kept as delivered.
- The submitted `SHA256SUMS` (not listed above) was verified in full (13/13) on filing (batch 57 of `docs/incoming/`) and not kept; the delivered archive remains in the repository history (see `docs/incoming/README.md`, batch 57 row).
- `README.md`: the reproduction command and output location, and this
  section. `CLAIMS_AND_VALIDATION.md`: an editorial note on the amplitude row.

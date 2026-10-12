# Summation and Singularities under Polylogarithmic Reversion

Research manuscript prepared for the ProveIt project, 12 October 2026.

Repository baseline: `8f5afd4d7565df808359f6a0c22f87f79a119bb9`.

## Read the article

The complete manuscript is `polylogarithmic_reversion.pdf`. Its source is
`polylogarithmic_reversion.tex` with the modular sources in `sections/`.
The bibliography is embedded in `sections/references.tex`; no BibTeX database
or network access is required to build the article.

The main contributions are:

1. An absolutely convergent sum of nonlinear-degree blocks, with radial Abel
   limits inside each block, reconstructs the harmonic depth-two angular zero
   for every real outer order at least 6. It comes with explicit uniform error
   bounds and a finite approximation with Gaussian accuracy in the outer order.
2. Uniform factorial convolution estimates prove the even/odd late-coefficient
   conjecture in the incoming resonant Lambert inverse report, including the
   first correction. An initial-disk Borel decomposition identifies both nearest
   logarithmic singularities for every nonzero complex coupling.
3. The direct inverse of the real-order polylogarithm has a holomorphic endpoint
   exactly at orders `s = 1 + 1/q`, integer `q >= 2`. The paper classifies minimal
   finite ramification, gives convergent exceptional Taylor charts, and disproves
   a proposed all-real-order extension of a cut-modulus inequality below `s=3/2`.

Classical inversion and continuation machinery is attributed. Novelty is stated
relative to the inspected repository corpus and a targeted primary-source
literature search. No exhaustive worldwide priority claim is made.

## Build

Requirements: Python 3.10 or later, the packages in `requirements.txt`, and a
standard TeX Live installation providing pdfLaTeX and latexmk. The TeX packages
used are listed in the main source preamble and are widely distributed.

```bash
python3 -m pip install -r requirements.txt
make pdf
```

The supplied tables and vector figure are already generated. To build without
Python or Make, run pdfLaTeX on the main source three times from this directory:

```bash
pdflatex -interaction=nonstopmode -halt-on-error polylogarithmic_reversion.tex
pdflatex -interaction=nonstopmode -halt-on-error polylogarithmic_reversion.tex
pdflatex -interaction=nonstopmode -halt-on-error polylogarithmic_reversion.tex
```

## Reproduce the finite checks

```bash
make checks
make pdf
```

Individual scripts can be run from any working directory. Outputs are written
beside the manuscript in `results/`. The angular integral calculations are the
slowest part of regeneration; no network access is needed.

| File | Purpose |
| --- | --- |
| `scripts/verify_angular.py` | Exact first degree polynomials and rational constants; 85-digit integral-root diagnostics and moving finite approximations |
| `scripts/verify_lambert.py` | Full finite Lagrange formula through degree 201 at 90-digit precision, including complex cancellation parameters |
| `scripts/verify_endpoint.py` | Exact comparison of formal reversion and Lagrange coefficients; direct numerical endpoint and cut-bank diagnostics |
| `scripts/make_figures.py` | Regenerates the three article tables and vector PDF/PNG figure from retained JSON outputs |
| `scripts/package.py` | Regenerates the integrity manifest and ZIP while excluding TeX auxiliaries |
| `results/*.json` | Machine-readable diagnostic outputs, with their precision and evidence scope |
| `AUDIT_AND_INTEGRATION.md` | Proposed status updates and integration guidance for existing reports |
| `PROVENANCE.json` | Immutable repository references and inspected source locations |
| `CLAIMS.md` | Theorem map, dependencies, and boundaries of the results |
| `VALIDATION.md` | Build, finite-check, and visual-inspection record |
| `SHA256SUMS.txt` | Integrity hashes for the package files |

The analytic theorems are proved in the article. The programs are supporting
checks, not proof-assistant formalizations. Numerical values are ordinary
high-precision diagnostics, not interval enclosures.

## Scope of integration

The package is self-contained and suitable for placing under `docs/incoming`
for review, or under a new research-report directory with cross-references from
both analysis areas. No repository files have been modified. The proposed
changes preserve valid existing theorems and distinguish a failed proposed
extension from an error in an established theorem. Thirteen further research
questions are developed in the article.

This manuscript was prepared with AI assistance for mathematical review before
incorporation into a collective manuscript. The source baseline and detailed
proofs are provided to make that review concrete.

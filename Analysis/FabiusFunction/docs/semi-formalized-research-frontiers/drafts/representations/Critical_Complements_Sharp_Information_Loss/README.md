# Critical Complements in Fabius Conditioning

**Sharp information loss, geometric phase constants, and a logarithmic crossover**

A 24-page research manuscript prepared for Vladimir Reshetnikov, dated
30 September 2026. The complete article is `article.pdf`; its editable
LaTeX source is `article.tex`.

## Research result

This continues the critical-complement question explicitly left open in
ProveIt's *Sharp Conditioning Laws for Uniform Random Series*. It resolves
its geometric-prefix version: fixed geometric ratio q, fixed exponential-tilt
phase rho, inequality conditioning at the tilted mean, and a prefix of n-m
bulk coordinates with m=o(n). The infinite boundary tail remains unobserved.

Theorem 2.1 gives a phase-sensitive two-term overlap expansion for fixed m,
a compact boundary correction with a controlled remainder, and relative
entropy through order 1/n with an O(n^-2) remainder. Theorem 2.2 proves the
leading overlap throughout the sublinear-complement regime and identifies
the crossover at m of order log n. Its coefficient is explicit through the
two real branches of Lambert W. Theorem 2.3 gives the entropy asymptotic for
growing m and identifies the fixed-complement information loss with the
mutual information of an additive exponential-noise channel.

All main results have conventional proofs. They are not Lean-certified or
externally refereed. The computations are diagnostics, not proof
certificates. Publication priority has not been established. Arbitrary
observation masks, general weights, and joint moving-q limits are not
silently included in the stated scope.

## Contents

- `article.tex`, `article.pdf`: manuscript, including proofs and bibliography.
- `code/verify.py`: deterministic floating-point boundary and finite-n checks.
- `code/make_figures.py`: builds the two figures and table fragments from data.
- `data/`: numerical CSV files, LaTeX tables, and the verification receipt.
- `figures/`: the two vector PDF figures used by the article.
- `CLAIM_STATUS.md`: proof and scope boundaries.
- `provenance.json`, `validation.json`: source and build records.
- `requirements.txt`, `Makefile`, `SHA256SUMS.txt`: reproduction support.

## Build the PDF

Use pdfLaTeX with standard TeX Live packages, including newtx, microtype,
the AMS packages, geometry, booktabs, fancyhdr, xurl, and hyperref:

```sh
make pdf
```

The figure PDFs and LaTeX table fragments are already supplied. Rebuilding
only the article needs neither Python nor network access. Font files are
not distributed.

## Rerun the calculations

```sh
python -m pip install -r requirements.txt
make diagnostics
```

`verify.py` uses Fourier inversion for the boundary CDF, exact analytic
exponential-tail formulas, and a signed Gamma formula for prefix densities.
There is no Monte Carlo. It computes the actual geometric-model formulas,
not a finite-simplex proxy, but finite grids, product truncation, numerical
integration, and floating-point arithmetic introduce approximations. The
reported grid agreement is not an interval-certified error bound.

For faster exploratory runs a smaller Fourier grid can be selected, for
example `python code/verify.py --grid-power 14`. The default is 15, with
comparison against a second grid of power 16. Running the script rewrites
the data receipt. Fixed source and library versions do not guarantee
byte-identical figure PDFs across platforms.

## Repository provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `0a543d5e435df885f78ca731d71856f3ee0ab2d4`.

The exact prior paths and the limited inspection scope are recorded in
`provenance.json`. No repository files were modified, and no Lean/Lake build
was run. The ten further research questions are in Section 10.

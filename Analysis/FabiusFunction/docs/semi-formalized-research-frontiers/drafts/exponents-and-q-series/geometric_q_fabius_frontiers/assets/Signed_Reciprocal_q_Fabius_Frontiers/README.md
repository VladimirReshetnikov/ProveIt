> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part VII** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/Signed_Reciprocal_q_Fabius_Frontiers/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

# Signed and Reciprocal q-Fabius Frontiers

This archive accompanies the research report
**Signed and Reciprocal q-Fabius Frontiers: Negative parameters, reciprocal
Laplace duality, two-nome Pochhammer-Prouhet partition functions, and
inverse-geometric endpoint lattices**.

The report was written after auditing the recursive LaTeX corpus under
`Analysis/FabiusFunction/docs` in the ProveIt repository, pinned at commit
`89b1a5f915cad065a42ee48f758eb2cd2d9beb94` (28 August 2026). Statements marked
"new relative to the pinned snapshot" mean that targeted full-corpus searches
and the canonical synthesis documents did not reveal the same result in that
snapshot. This is a corpus-relative novelty statement, not a claim of global
literature priority. Theorems proved in the report and conjectures/open problems
are labeled separately.

## Main contents

The 39-page report develops a normalized geometric-uniform law

```text
Y_q = (1-q) sum_{j>=0} q^j U_j,
```

whose `q=1/2` case is the Fabius distribution, and then studies the complete
sign/reciprocity orbit `q, -q, 1/q, -1/q`. The main results include:

- exact affine transport from positive to negative contraction parameters;
- the reciprocal identity `M_q(t) M_{1/q}(-t)=1` and an explicit infinite
  Laplace-convolution representation of reciprocal centered germs;
- a `q^2`-Pochhammer spectral factorization of the generalized Rvachev
  characteristic product, including zero-multiplicity formulas;
- geometric multisection and the dyadic-to-quartic independent-sum/convolution
  decomposition;
- a q-Fabius-Bernoulli Appell family that inverts geometric-uniform averaging;
- a pole-cleared moment polynomial `P_n(q)` and exact symbolic evidence through
  `n=16` for its conjectural odd-q-integer divisor;
- a two-nome binary-cube partition function simultaneously containing the
  Gaussian-binomial/Pochhammer and Thue-Morse/Prouhet faces;
- an exact geometric q-Prouhet moment-transfer theorem;
- signed box-spline derivative combs, including the quartic Cantor skeleton;
- exact inverse-geometric endpoint values and derivative jets for every
  `0 < q <= 1/2`, including the inverse-quartic lattice at `q=1/4`;
- rigorous two-term endpoint and inverse asymptotics, followed by labeled
  Lambert-W, natural-boundary, arithmetic, and orthogonal-polynomial programs.

The eight parameter values requested in the task,
`-1/2, 1/2, -2, 2, -1/4, 1/4, -4, 4`, are treated explicitly.

## Archive layout

```text
Signed_Reciprocal_q_Fabius_Frontiers.tex  LaTeX source
Signed_Reciprocal_q_Fabius_Frontiers.pdf  compiled report
numerical_experiments.py                  exact and high-precision checks
requirements.txt                          Python dependencies
assets/*.png                              five deterministic figures
data/*.csv                                exact values and residual tables
SHA256SUMS.txt                            checksums for archive payload files
```

The Python program is extensively commented and deliberately avoids a symbolic
algebra dependency. Exact work uses `fractions.Fraction` and integer polynomial
arithmetic; `numpy`, `matplotlib`, and `mpmath` are used only for numerical
checks and deterministic figures. No random sampling is used.

## Rebuild the report

Run from the archive directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  Signed_Reciprocal_q_Fabius_Frontiers.tex
```

The tested build environment used pdfTeX 1.40.26 and latexmk 4.86 from a TeX
Live 2025 development installation. The source uses common TeX Live packages:
`geometry`, `fontenc`, `inputenc`, `libertinus` (with an `lmodern` fallback),
`microtype`, AMS math packages, `mathtools`, `mathrsfs`, `bm`, `booktabs`,
`longtable`, `tabularx`, `array`, `multirow`, `graphicx`, `float`, `caption`,
`subcaption`, `xcolor`, `enumitem`, `fancyhdr`, `titlesec`, `xurl`, `listings`,
`hyperref`, and `cleveref`.

## Reproduce the calculations and figures

Python 3.10 or newer is required. Install the small dependency set and run:

```bash
python -m pip install -r requirements.txt
python numerical_experiments.py
```

The tested environment used Python 3.13.5, NumPy 2.3.5, Matplotlib 3.10.8, and
mpmath 1.3.0. A successful run prints:

```text
All exact and high-precision checks passed.
```

It regenerates every CSV under `data/` and every PNG under `assets/`. The exact
checks include orbit transformations, moment recurrences, reciprocal
convolution inversion, q-to-q-squared decimation, Gaussian position-energy
layers, the q-Prouhet theorem, endpoint values, finite-field/unitary
normalizations, Hankel signatures, and the moment-polynomial divisibility
experiment. Analytic product identities are checked at 90 decimal digits.

## Validation performed for this archive

- LaTeX completed with no overfull/underfull boxes, unresolved references,
  missing characters, or PDF bookmark warnings.
- The PDF has 39 A4 pages and all fonts are embedded.
- Every page was rendered at 200 dpi and visually inspected.
- PDF preflight reported no warnings.
- The numerical program was rerun from scratch and all exact/high-precision
  checks passed.
- The final ZIP was rebuilt and tested from a clean extraction.

> **Editorial note (2026-08-28):** the report source and compiled PDF listed above (and, where listed, the supplied source scan/OCR) were removed from this directory after their content was merged into the volume `Exponents_and_q_Series_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance list (and in `SHA256SUMS` here where present), and git history archives the files. This directory keeps only figures, data, and scripts.

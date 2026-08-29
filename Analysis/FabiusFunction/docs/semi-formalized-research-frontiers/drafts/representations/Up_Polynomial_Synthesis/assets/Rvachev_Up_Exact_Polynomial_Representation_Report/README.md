# Exact Polynomial Plateaux from Rvachev's Up-Function

This archive accompanies the research report on exact finite representations of an arbitrary polynomial on a prescribed interval by shifted and scaled copies of Rvachev's `up` function.

## Main construction

Let `up` be the even compactly supported function on `[-1,1]` normalized by

```text
Fourier[up](xi) = product_{n>=0} sinc(pi*xi/2^n),
integral up = 1.
```

For a degree-`d` polynomial `p`, choose an integer `m` with `v2(m) >= d`, a lattice step `h > 0`, a lattice origin `x0`, and set `rho = m*h`.  Define

```text
M(z) = product_{j>=1} sinh(z/2^j)/(z/2^j),
p_sharp = M(rho*D)^(-1) p.
```

The inverse operator is a finite differential operator on polynomials.  Then

```text
p(x) = (1/m) * sum_{k in Z} p_sharp(x0+k*h)
                         * up((x-x0-k*h)/rho).
```

The sum is locally finite.  On an interval `[A,B]`, it is enough to keep

```text
ceil((A-x0)/h - m) <= k <= floor((B-x0)/h + m).
```

The report proves that the stationary reproduction degree is exactly `v2(m)`, so the smallest integer ratio for degree `d` is `m = 2^d`.

## Reproducing the computations

From this directory, run:

```bash
python rvachev_polynomial_reproduction.py
```

The script uses exact `fractions.Fraction` arithmetic for every coefficient and verification value.  Matplotlib is optional and is used only to regenerate `representation_plot.png`; use `--no-plot` to skip it.

To rebuild the PDF with TeX Live and `latexmk`:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  Exact_Polynomial_Plateaux_from_Rvachev_Up.tex
```

## Verified example

The included degree-four example uses

```text
p(x) = 7/5 - 3*x + 2*x^2 - x^3/2 + 3*x^4/7,
I = [-1/2, 3/2],
m = 16,
h = 1/8,
rho = 2.
```

It produces 49 atoms.  Exact evaluation at 129 dyadic points gives maximum residual `0`.  Additional deterministic tests for all degrees from 0 through 6 also give exact residual `0`.

## Files

- `Exact_Polynomial_Plateaux_from_Rvachev_Up.tex` — complete report source.
- `Exact_Polynomial_Plateaux_from_Rvachev_Up.pdf` — rendered report.
- `rvachev_polynomial_reproduction.py` — commented exact construction and verification code.
- `example_coefficients.csv` — all 49 coefficients of the worked example.
- `exact_grid_check.csv` — 129 exact pointwise checks.
- `appell_coefficients_m16.csv` — up-Appell coefficients through degree 8 for `m=16`.
- `generic_degree_checks.csv` — exact checks for degrees 0 through 6.
- `verification_summary.txt` — concise verification output.
- `representation_plot.png` — plot used in the report.
- `SHA256SUMS` — integrity hashes.

## Repository snapshot

The report audited the LaTeX corpus under `Analysis/FabiusFunction/docs` in `VladimirReshetnikov/ProveIt`, pinned to commit:

```text
5915d9a723c9ae01a2cc4be8a251bdcb11d9e406
```

The final audit covered all 97 LaTeX sources in that snapshot.  The report explicitly treats the repository's existing Rvachev--Appell deconvolution, dyadic Strang--Fix exactness, self-sampling rules, and alias hierarchy as prior corpus inputs.  Its corpus-relative additions are the finite interval-synthesis algorithm, explicit truncation/support/atom-count bounds, common-scale obstruction and complexity results, ghost-antiderivative construction, Thue--Morse derivative stencil, finite-prefix transfer, and tensor-product extension.  No unconditional claim of world priority is made.

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Up_Polynomial_Synthesis.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.

# Dyadic-Comb Sums for the Fabius-Rvachev System

This package contains the research report, its compiled PDF, and the exact/high-precision experiment program used to check and regenerate its tables.

## Contents

- `Fabius_Dyadic_Comb_Sums_Report.tex` — complete LaTeX source.
- `Fabius_Dyadic_Comb_Sums_Report.pdf` — rendered 25-page report.
- `dyadic_comb_experiments.py` — commented exact-arithmetic and high-precision verification program.
- `generated/` — regenerated CSV data and LaTeX table fragments.
- `requirements.txt` — Python dependencies.
- `SHA256SUMS.txt` — checksums for the package files.

## Audit boundary

The mathematical corpus audit is pinned to ProveIt commit

`fa53516af8cbe7d792a97b25378b228b96e37cf9`

from 28 August 2026. The audit treats recursively embedded copies and historical revisions by mathematical lineage, using the repository source ledger, the live primary documents, and the consolidated inverse/sampling, integration/transform, and representation volumes. Novelty language in the report is intentionally snapshot-relative, not a claim of universal priority.

## Main proved results

The report develops:

1. a rational ordinary generating function for the complete level-`N` Fabius sample row, including exact cancellation of `N` apparent poles and a constant tail equal to one;
2. a finite Bernoulli-Thue-Morse formula for every natural monomial power, and a Bell-Prouhet compression reducing the signed part to at most `p+2` terms;
3. an exact Euler-Maclaurin identity for the ordinary dyadic Fabius comb through degree `2 floor(N/2)`;
4. the first odd-level defect as a half-integer sinc-product Dirichlet series with Thue-Morse signs;
5. exact Hurwitz-zeta forms for complex powers and rational formulas for negative integer powers;
6. logarithmic and zeta-dominated asymptotics for punctured Rvachev combs at negative powers;
7. an exact unsigned-Stirling reduction of an `n`-fold prefix sum to shifted one-fold combs, plus a fractional Gamma-kernel continuation.

Conjectures and future directions are clearly separated from proved statements.

## Reproduce the tables and checks

Python 3.11 or later is recommended. The package was tested with Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0.

```bash
python -m pip install -r requirements.txt
python dyadic_comb_experiments.py --outdir generated --max-level 8
```

The program independently compares:

- direct exact dyadic convolution;
- the exchanged Bernoulli/Faulhaber formula;
- the Bell-Prouhet coefficient collapse;
- direct and Stirling-reduced iterated sums;
- exact Euler-Maclaurin identities;
- odd-level Fourier-defect formulas at high precision.

A successful run ends with:

```text
All checks passed.  Generated files are in .../generated
```

## Build the PDF

A recent TeX Live installation with `latexmk`, `libertinus`, `tcolorbox`, `cleveref`, and the standard AMS packages is sufficient. From this directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  Fabius_Dyadic_Comb_Sums_Report.tex
```

The source expects the generated table fragments under `generated/`, so run the Python program first when rebuilding from a clean checkout.

# Inverse q-Analogs report archive

This archive accompanies **Inverse q-Analogs: Branch Geometry, Asymptotic
Inversion, and Computation for q-Pochhammer Symbols, Gaussian Coefficients, and
Related Functions**.

## Main files

- `inverse_q_analogs_report.tex` — complete LaTeX source.
- `inverse_q_analogs_report.pdf` — compiled 73-page report.
- `numerical_experiments.py` — documented, deterministic Python program that
  regenerates the symbolic factorizations, numerical tables, and vector
  figures.
- `requirements.txt` — Python dependencies.
- `data/` — CSV and text outputs used to audit the numerical statements.
- `figures/` — generated vector PDF figures included by the LaTeX source.

## Reproduce the experiments

```bash
python3 -m pip install -r requirements.txt
python3 numerical_experiments.py
```

The script uses 60-decimal-digit `mpmath` arithmetic for the high-precision
root calculations and exact `sympy` polynomial arithmetic for the secondary
discriminants. No network access or random sampling is used.

## Rebuild the report

A reasonably complete TeX Live installation with `latexmk` is sufficient:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  inverse_q_analogs_report.tex
```

## Status conventions

The report labels statements as **proved**, **symbolic/numerical**, or
**conjectural**. Exact polynomial factorizations are reproducible algebraic
identities. Decimal sheet identifications and asymptotic tests are
high-precision evidence, not interval-certified proofs.

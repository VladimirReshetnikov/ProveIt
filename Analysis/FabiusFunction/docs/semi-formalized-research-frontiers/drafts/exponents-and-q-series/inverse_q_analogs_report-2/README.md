# Inverse functions of q-analogs — report bundle

This archive contains a self-contained research report on inverses of finite and
infinite q-Pochhammer symbols, Gaussian q-binomial coefficients, q-gamma and
related q-analogs with respect to q and their other parameters.

## Files

- `inverse_q_analogs_report.tex` — complete LaTeX source.
- `inverse_q_analogs_report.pdf` — rendered 59-page report.
- `inverse_q_analogs_experiments.py` — commented symbolic and high-precision
  numerical checks.
- `numerical_results.txt` — output produced by the Python script and included
  verbatim in the report.
- `SHA256SUMS.txt` — checksums for integrity verification.

## Reproduce the numerical checks

The script requires Python 3, SymPy, and mpmath. From this directory, run:

```bash
python3 inverse_q_analogs_experiments.py
```

The script prints its results and regenerates `numerical_results.txt` next to
itself. The calculations use 80 decimal digits. They are validation checks, not
substitutes for the proofs in the report.

## Rebuild the PDF

A TeX Live installation with `latexmk` and standard LaTeX packages is
sufficient. Run the Python script first, then:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error inverse_q_analogs_report.tex
```

The source has no external figure or bibliography-file dependencies.

## Scope and status conventions

The report separates proved statements, newly derived asymptotic formulas, and
explicitly labelled conjectures. Branch choices, exceptional low-degree cases,
and domains of validity are stated near the relevant formulas.

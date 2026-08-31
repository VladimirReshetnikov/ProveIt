# Interpolation on a Geometric Comb

> **Source-only merge status (2026-08-31).** The current TeX has 2,360 lines
> (SHA-256
> `d161dc81b07589245f60587db22a9a0ae7cac43c28654d396d2528a1d79d6bff`).
> The retained 32-page PDF was not rebuilt after the notation migration and is
> not claimed to be synchronized with that source. `SHA256SUMS.txt` was
> intentionally not refreshed: its TeX row and this README row are pending,
> while its other fifteen rows pass. Historical build facts below describe the
> preceding checkpoint.

This package contains the deeply audited report
*Interpolation on a Geometric Comb: Lagrange and Newton Formulas, Jackson
Calculus, Modal Filters, Geometric B-Splines, and Fabius--Rvachev Connections*
(30 August 2026).

## Status

The report has manuscript proofs for its 37 labelled nonconjectural results
(25 theorems, three propositions, one lemma, and eight corollaries). It also
contains two explicitly marked conjectures and five explicitly marked research
problems. A hostile read found no fatal counterexample or false theorem label,
but this is not a claim that the complete report has been formalized.

The finite Gaussian-comb core has independently checked Lean coverage in the
repository. The opening status box and the formalization roadmap identify that
coverage and distinguish it from report-specific results that remain
manuscript mathematics. See `REPOSITORY_AUDIT.md` for the exact crosswalk and
audit limits.

The retained PDF is a 32-page A4/27 mm Libertinus artifact. At the preceding
checkpoint it was built from the then-frozen source with exactly three strict
serial `pdflatex` passes. All
fonts are embedded and subset, there are no Type 3 fonts, references are
resolved, extracted text is clean, and every rendered page was inspected. See
`PDF_VALIDATION.txt`.

## Arrival provenance

The first observable package state was verified against its self-excluding
11-entry checksum ledger. That exact ledger is preserved as
`SHA256SUMS.arrival.txt` (SHA-256
`eab71028a18157e98c36278b987009421c9eb79b7abb902c21a4986beb16477d`).
The arrival source and PDF hashes were respectively
`79d2f7fe05c457c207254ec35a8d18d880364a63b0e01b56181e1d7a599e1d65`
and
`a990c74070dbaf5a79c9840ec8a3cd30a757b651dbd94db0f4bd7bc02cabc036`.
No outer source archive is retained in, or available to, this package, so no
outer-archive name, size, or hash is inferred. `ARRIVAL_MANIFEST.txt` is
reconstructed solely from the verified arrival ledger.

## Reproducing the computations

Use a fresh Python environment. The direct dependencies are in
`requirements.txt`; the exact successful transitive environment is in
`requirements-lock.txt`.

```bash
python -m venv .venv
.venv/bin/python -m pip install -r requirements-lock.txt
.venv/bin/python geometric_comb_experiments.py
```

The pinned replay used CPython 3.13.14, `mpmath==1.4.1`, and
`matplotlib==3.10.8`. It reproduced all four CSV files and all three PNG files
byte for byte. The script uses exact rational arithmetic where applicable and
140-decimal-digit `mpmath` arithmetic elsewhere. Its generated text files use
LF line endings, and its plotting backend is noninteractive.

## Rebuilding the report

From this directory, run three strict serial passes:

```bash
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error geometric_comb_interpolation_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error geometric_comb_interpolation_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error geometric_comb_interpolation_report.tex
```

The frozen archival build completed all three passes. Its remaining warnings
are harmless `hyperref` PDF-bookmark string warnings for mathematics in section
titles and three underfull bibliography lines. There are no overfull boxes,
undefined references or citations, rerun requests, or TeX errors.

## Files

- `geometric_comb_interpolation_report.tex`: current source;
- `geometric_comb_interpolation_report.pdf`: retained preceding-checkpoint PDF,
  pending rebuild;
- `geometric_comb_experiments.py`: experiment and figure generator;
- `moment_checks.csv`, `stability_growth.csv`, `regular_variation.csv`, and
  `fabius_boundary.csv`: archived numerical tables;
- `stability_growth.png`, `regular_variation_convergence.png`, and
  `fabius_boundary_ratio.png`: archived figures;
- `requirements.txt` and `requirements-lock.txt`: direct and exact replay pins;
- `ARRIVAL_MANIFEST.txt` and `SHA256SUMS.arrival.txt`: arrival provenance;
- `REPOSITORY_AUDIT.md` and `PDF_VALIDATION.txt`: deep-audit records;
- `SHA256SUMS.txt`: unrefreshed 17-entry operational ledger, excluding itself;
  its TeX and README rows are pending.

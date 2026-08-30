# Inverse q-Analogues

This directory retains the audited research-frontier report *Inverse
q-Analogues: Branch Geometry, Asymptotic Inversion, and Computation for
q-Pochhammer Symbols, Gaussian Coefficients, and Related Functions*.

The report is a paper-level mathematical companion, not a Lean-backed primary
exposition. Its green `paper proof` tag means that the report supplies a proof
or invokes a cited mathematical theorem; it does not mean that Lean checked the
claim. The live formal corpus provides selected finite Gaussian/Pochhammer
algebra and infinite-product convergence, but none of this report's specialized
inverse, critical-atlas, discriminant/Maxwell, monodromy, branch-geometry, or
inverse-asymptotic theorems has an exact public Lean counterpart.

## Files

- `inverse_q_analogs_report.tex` and `inverse_q_analogs_report.pdf` are the
  canonical 51-page A4/27 mm/Libertinus source and artifact.
- `numerical_experiments.py` regenerates all seven data files and five vector
  figures without network access or random sampling.
- `data/` and `figures/` contain the generated audit evidence used by the
  report.
- `REPOSITORY_AUDIT.md` records the hostile mathematical and formal-corpus
  review, including the repaired claims and exact Lean boundary.
- `COMPILE_TRANSCRIPT.txt` and `PDF_VALIDATION.txt` record the final build and
  artifact checks.
- `ARRIVAL_SHA256SUMS.txt` is a repository-generated historical ledger for the
  17 delivered files; `SHA256SUMS.txt` is the current 21-file ledger.

## Provenance

The package arrived on 2026-08-30 as
`drafts/incoming/inverse_q_analogs_report.zip` (894,405 bytes; SHA-256
`471ee715022df77f2c5f45b86c213e50e980478eee1a6fc48dd91556cdaeb627`).
The archive contained 17 files beneath one safe wrapper directory and no
submitted checksum ledger. Archive integrity and path safety passed, and all
17 extracted files matched the recovered archive before normalization. The
repository-created arrival ledger preserves those hashes without pretending it
was supplied by the author.

## Reproduce the computations

Use Python 3 with the versions or compatible lower bounds in
`requirements.txt`:

```bash
python3 -m pip install -r requirements.txt
python3 numerical_experiments.py
```

The intake replay used CPython 3.13.14, `mpmath` 1.3.0, `sympy` 1.14.0,
`numpy` 2.3.5, and `matplotlib` 3.10.8. All seven generated data files were
byte-identical to arrival before repository normalization; five CSVs are
stored with LF endings, and the generator now reproduces those normalized
bytes. The five regenerated plots preserved the plotted content and now
request embedded TrueType PDF text instead of Matplotlib's disallowed Type 3
default.

## Rebuild the report

From this directory, start without LaTeX auxiliaries and run exactly three
serial passes:

```bash
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error inverse_q_analogs_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error inverse_q_analogs_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error inverse_q_analogs_report.tex
```

The frozen final-source build produced 51 A4 pages. The final log has no
errors, warnings, unresolved references or citations, rerun requests, duplicate
destinations, or overfull/underfull boxes. All 34 reported font rows are
embedded and subset; six rows are Libertinus, no row is Type 3, and no Latin
Modern font is present. All pages have zero rotation. LaTeX auxiliaries are not
retained.

## Audited claim boundary

The audit corrected an unattained order-inverse endpoint, strengthened the
safeguarded-Newton hypotheses and acceptance rule, restored the missing
near-unit-base logarithmic factor in the truncation cost, and made the radicals
claim conditional on proved symmetric monodromy. It also weakened an
over-broad q-Bessel/q-Airy sentence, removed a priority implication, and kept
the order-six sheet identification explicitly numerical rather than
interval-certified. Exact polynomial factorizations remain algebraic; decimal
sheet identifications and asymptotic tests remain high-precision evidence.

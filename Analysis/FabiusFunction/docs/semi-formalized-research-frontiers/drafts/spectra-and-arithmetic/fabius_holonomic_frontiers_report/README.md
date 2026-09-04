# Holonomic Rank, Exact Overlaps, and Non-P-Recursiveness
## Frontier results for the Fabius-Rvachev system

This package contains the LaTeX source, compiled 30-page PDF, exact/high-
precision experiment code, generated certificates, plots, and corpus-audit
notes for the report prepared on 30 August 2026.

## Principal report-level results

The proved layer develops:

- an exact formula for the minimal rational-coefficient differential order of
  every finite geometric sinc product, in terms of a signed finite Bernoulli
  convolution;
- a rank-knot duality identifying that differential rank with the number of
  atoms surviving in the highest distributional derivative of the associated
  box spline;
- a restricted-coefficient polynomial criterion for rank defects, an exact
  frequency-gap formula for `q <= 1/2`, and existence/detection of a signed
  holonomic entropy;
- the complete minimal dyadic operator, its Thue-Morse spectral coefficient
  vector, its Pochhammer factorization, Bell-Bernoulli coefficient formulae,
  and Barnes-G discriminant;
- non-D-finiteness of the infinite integer-base sinc products from unbounded
  zero multiplicities, plus escape of the dyadic logarithmic derivative from
  every finite dyadic trigonometric rational field;
- non-P-recursiveness of the Rvachev moment, cumulant, reciprocal-moment, deep
  dyadic Fabius sample, and fixed-order derivative-sample sequences;
- an order-zero, entire, non-D-finite ordinary generating function for the
  deep dyadic samples.

The inverse-golden-ratio rank recurrence, differential transcendence, inverse-
Fabius sample obstruction, and refined order-zero saddle asymptotics are
clearly labelled as conjectures or research problems rather than theorems.

## Rebuild

```bash
python frontier_experiments.py --output-dir data
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_holonomic_frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_holonomic_frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_holonomic_frontiers.tex
```

Python dependencies are listed in `requirements.txt`. The report uses a
standard TeX Live installation with `pdflatex`, Libertinus, AMS,
`hyperref`, `cleveref`, `listings`, and the usual graphics/table packages.
The TeX source uses the retained PNG companions under `data/`; the vector PDFs
remain as reproducibility assets.

## Files

- `fabius_holonomic_frontiers.tex` - complete report source.
- `fabius_holonomic_frontiers.pdf` - compiled report.
- `frontier_experiments.py` - deterministic, commented experiment suite.
- `data/` - exact CSV/TXT/TeX certificates and PDF/PNG figures.
- `CORPUS_AUDIT.md` - repository snapshot, exclusions, and novelty protocol.
- `NUMERICAL_README.md` - experiment status and tested versions.
- `VALIDATION.md` - build, font, render, and reproducibility checks.
- The former `SHA256SUMS` payload ledger was retired repository-wide on
  2026-09-01; its final snapshot remains recoverable from Git history.

“Novel” in the report means novel relative to the audited repository corpus.
The package does not assert absolute historical priority without a dedicated
claim-by-claim literature review.

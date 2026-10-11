# Bilinear Mellin–Hurwitz Calculus

**Double-zeta reductions, harmonic moments, and Stieltjes reciprocity**  
Research continuation for ProveIt, 10 October 2026.

## Read first

`article.pdf` is the complete article. `article.tex`, `sections/`, and
`references.tex` are its editable LaTeX source. This is one manuscript,
not a collection of unrelated reports.

The article continues the tenth research question in the repository's
Mellin–Lerch/Stieltjes-dilation report. It proves the positive-integer-order
finite-multiple-polylogarithm closure sector, including the full admissible
integer Mellin strip. At equal arguments it supplies stronger finite
common-shift double-Hurwitz formulas, all logarithmic moments at a=0 and a=-1,
a terminating recurrence for all denominator orders and integer Mellin
parameters, weighted MZV identities, explicit primitives, central parity
reductions, and Stieltjes spectral-derivative identities.

**Scope:** arbitrary complex polylogarithm orders and arithmetic minimal
depth are not settled by the finite-closure theorem. The Gaussian S6 and S8
conjectures are unchanged. Generic hyperlogarithmic integration, the
one-factor Mellin theorem, and classical Gamma and inversion identities
are explicitly credited. Historical priority beyond the inspected sources,
external peer review, and proof-assistant formalization are not claimed.

## Completed verification

- 8,849 exact checks passed. The file `data/exact_results.json` records the
  categories and software version.
- 67 independent numerical comparisons passed at 45 decimal working digits.
  Maximum scaled discrepancy: less than 2.3e-44. The threshold was 1e-33.
  `data/numerical_results.json` contains each pair of values and its residual.
- Numerical residuals are diagnostics, not interval certificates or proofs.
  The infinite identity families are proved in the article. The Stieltjes
  spectral and continuous-primitive extensions are not represented as having
  direct quadrature coverage in the 67-case suite.
- `data/formula_table.json` is an exact generated identity catalogue, not an
  experimental PSLQ store.

## Reproduce

Use a copy of the delivery when replaying scripts, so the preserved evidence
is not overwritten. Python 3.10 or later is expected; the tested version is
3.13.5. Install the pinned dependencies using your usual virtual environment:

```sh
python -m pip install -r requirements.txt
python verification/verify_exact.py
python verification/verify_numerics.py
python verification/export_tables.py
python build.py
```

The verification scripts also accept `--output /path/to/result.json`.
The numerical suite can take several minutes. Its double-Hurwitz evaluator
supports real q>0 and integer indices A>=2, B>=1; the analytic theorem also
covers complex q with positive real part. At integer Mellin parameters use
the resonance or kernel functions rather than a floating-point cosecant limit.

`build.py` requires pdfLaTeX and the packages listed in `article.tex`.
It runs three passes and rejects unresolved citations/references. The PDF was
rendered and visually inspected after compilation. Font files are not included.

## Files

- `verification/mellin_exact.py`: finite coefficient and Laurent-kernel calculus.
- `verification/mellin_numeric.py`: independent double-Hurwitz and quadrature evaluators.
- `verification/verify_exact.py`: enumerated combinatorics and exact algebra.
- `verification/verify_numerics.py`: 67 direct comparisons and refinement checks.
- `verification/export_tables.py`: regenerate the exact identity catalogue.
- `AUDIT.md`, `PROVENANCE.json`: research status and source-inspection scope.
- `integration/INTEGRATION.md`: placement, label, and open-question update guidance.

Hurwitz zeta has a semicolon in the article, zeta(s;q); commas denote
multiple-zeta indices. In the symbolic JSON/code, `Z(A,B)` denotes a
convergent decreasing-index double zeta value, not single Hurwitz zeta.

No repository file was modified by this delivery. The intake and subsequent
canonical analytic review remain separate operations.

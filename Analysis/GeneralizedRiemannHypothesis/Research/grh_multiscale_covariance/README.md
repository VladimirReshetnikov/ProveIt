# Strict multiscale covariance of smoothed prime errors

Research note, 2026-11-26.

## Contents
- `report.tex`, `report.pdf`: complete mathematical proof and source analysis.
- `sources.md`: inspected repository files, immutable revision, related literature and limitations.
- `numerical_check.py`: reproducible q=3 prime-power experiment (no zero data needed).
- `numerical_results.json`, `covariance_example.csv`, `numerical_run.txt`: generated outputs of the default numerical run.
- `requirements.txt`: Python packages for the experiment.
- `SHA256SUMS`: hashes of deliverable files.

## Rebuild
Run `pdflatex -interaction=nonstopmode -halt-on-error report.tex` twice, with a standard TeX Live distribution and the packages used in the preamble.

To rerun the illustration, use Python 3.10 or later:

```sh
python -m pip install -r requirements.txt
python numerical_check.py
```

The program enumerates prime powers up to the largest evaluated argument, computes the exact finite sum structure with floating-point arithmetic, uses analytic centering constants (mpmath), and outputs sample covariance matrices/eigenvalues. The rational-scale atom collision checks are exact integer/rational checks; the covariance values are not rigorously certified limiting quantities. The example is independent of the analytical proof.

## Status and limitations
The paper proves an implication from Dirichlet GRH using standard classical analytic number theory, as supplied by the upstream machine-verified statement. It does not claim a new Lean formalization, a local upstream rebuild, resolution of unsmoothed prime-race inclusivity, or exhaustive bibliographic originality. The new proof is presented for mathematical review, with explicit hypotheses and a finite-deletion extension. The research direction (smoothed prime errors and multiscale covariance) was selected for this request.

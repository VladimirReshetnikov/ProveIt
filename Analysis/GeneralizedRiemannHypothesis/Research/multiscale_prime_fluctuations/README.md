# Spectral coercivity of multiscale smoothed prime-counting errors

Research note, 26 November 2026.

**Main result:** For fixed modulus and any finite collection of distinct logarithmic shifts, the centered square-root-normalized smoothed prime-power remainders have positive definite joint logarithmic covariance, even after deleting finitely many zero frequencies. For every sufficiently high positive-ordinate band of width H between K log(2T) and T, its spectral energy is bounded below by c H/(T^4 log(2T)) times the squared coefficient norm and above by C H log^2(2T)/T^4 times that norm. The proof uses Dirichlet GRH and classical analytic tools, not simplicity or rational independence of zeros. The multiscale formulation is independently derived; priority has not been established.

## Files

- `paper.tex`, `paper.pdf`: self-contained mathematical argument with explicitly cited classical inputs, source analysis, consequences, limitations, and further research questions.
- `source_audit.md`: inspected source paths, blob hashes, theorem dependencies and external references.
- `verify_examples.py`: exact rational arithmetic probe checks for q=12 and numerical zeta-only sanity checks.
- `prime_probes.csv`: 64 exact checks of prime-power separation.
- `zeta_ordinates.csv`, `zeta_ramp_examples.csv`, `zeta_covariances.csv`: approximate numerical outputs (not rigorous zero enclosures).
- `verification.txt`: captured output of the actual execution.
- `SHA256SUMS`: integrity hashes for the delivered content.

## Reproduce

```
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
python -m pip install numpy mpmath
python verify_examples.py
```

The calculations were run with Python 3, NumPy 2.3.5 and mpmath 1.3.0. The LaTeX source uses standard TeX Live packages including xurl, lmodern, amsmath, amsthm, microtype and hyperref. The new mathematical argument is not Lean-verified and no effective numerical values for the asymptotic constants are certified. The source review is targeted; the full upstream library was not replayed locally.

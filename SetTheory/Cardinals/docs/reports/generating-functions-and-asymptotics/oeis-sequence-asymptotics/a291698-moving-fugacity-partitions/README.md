# Moving fugacity asymptotics for distinct partitions

The main deliverables are:

- `output/pdf/moving-fugacity-report.pdf`: the complete research report
- `moving-fugacity-report.tex`: its editable standalone LaTeX source
- `REPRODUCIBILITY.md`: methods, commands, dependency versions, and the exact scope of each check
- `theorem-and-proof.md`: the preserved mathematical source used for integration

The theorem applies to `[q^n] product_(k>=1)(1+n^alpha q^k)`, uniformly when alpha lies in a fixed compact subset of `(0,infinity)`. OEIS A291698 is the alpha=1 case; A292304 is alpha=2.

## Results

The report includes an exact-dilogarithm Bessel hierarchy, resonance-safe minor arcs, an exact Jacobi transformation, rigorously separated local exponential sectors, and a specified real continuation with a controlled inverse. It proves the two displayed OEIS leading equivalents and explains the separate alpha=1/2 threshold for simplifying the dilogarithm.

## Replay

With the dependencies in `requirements.txt` installed, run:

```
python checks.py --max-n 20000 --output checks.json
python resonance_check.py
python validate.py
python sector_integrals.py
bash build_pdf.sh
```

The numerical programs use exact integer polynomial coefficients and high-precision evaluation. `validate.py` adds an independent direct-product method, public sequence-term checks, Jacobi-identity tests, and inverse comparisons. `sector_integrals.py` is uncertified high-precision quadrature.

## Scope

The sector count and algebraic depth are fixed before n tends to infinity. The principal approximation can have a late numerical onset, especially for alpha=2. No infinite Bessel-sector inversion, growing-sector theorem, interval-certified quadrature, or explicit finite-input big-O constants are asserted. An approximate continuous inverse must not be rounded across an unresolved integer boundary.

The work makes no publication-priority or external-peer-review claim. The latest literature comparison includes the Arabi Ardehali–Rosengren q-product paper published on 19 September 2026.

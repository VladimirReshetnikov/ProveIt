# Fresh verification, October 12, 2026

All five supplied programs ran to completion on an isolated copy, using
Python 3.13.5 with mpmath 1.3.0, NumPy 2.3.5, SciPy 1.17.0, SymPy 1.14.0
and Matplotlib 3.10.8. The complete default grids were retained, including
the optional local complex-fold diagnostic at X=40 and 180 digits.
Original delivered programs, data, figures and PDFs were not overwritten.

The fresh checks include eight exact coefficients against the original
implicit equation, 24 finite phase rows, 27 coefficient crossover rows,
three independent density comparisons, 12 critical inverse-chart cases,
nine order-crossover cases, 18 joint real cases, six negative-feedback
branch checks and the local complex fold. The critical-chart program's
symbolic logarithmic assertions pass. All 14 recorded-outcome checks in
[receipt-checks.json](receipt-checks.json) pass.

Windows NumPy longdouble has 15 decimal digits on this machine. The
independent 75-digit coefficient comparison differs by about 1.27e-15,
within the supplied precision-dependent tolerance. At n=2048 the marginal
coefficient/leading ratio is 0.7391197130; including the second logarithmic
correction gives 1.0100756567. These finite errors are retained explicitly.
The largest joint real relative residual is 3.73e-112, and the largest
critical-chart scaled residual is 1.89e-149. These are numerical diagnostics,
not certified error bounds. The complex fold's small equation residual
does not make its leading asymptotic constants equally accurate.

To check the recorded outcomes without rerunning the numerical programs:

```powershell
py -X utf8 intake-verification/check_receipts.py
```

To replay all five suites from the report directory with the declared
dependencies, choose a new output directory outside the preserved evidence:

```powershell
uv run --no-project --python 3.13 --with mpmath==1.3.0 --with numpy==2.3.5 --with scipy==1.17.0 --with sympy==1.14.0 --with matplotlib==3.10.8 python intake-verification/replay.py --output-directory C:/Users/vresh/AppData/Local/Temp/feedback-replay-new
```

The runner refuses an existing output directory, copies the delivered
package to a new temporary directory and executes only that copy.
Its process-success record is separate from the outcome assertions.
The original fresh-run commands, timings and full logs are preserved here.
The [analytic proof audit](../INTAKE-PROOF-AUDIT.md) supplies the mathematical
reasoning; this directory makes no general theorem, interval, Lean or
remote-CI claim.

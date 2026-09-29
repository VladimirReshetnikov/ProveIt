# Signed Condensation in Quadratic-Feedback Transseries

**Sharp reversion, universal cancellation, and inverse Borel growth**  
Research report prepared for Vladimir Reshetnikov, September 29, 2026.

## Main result

For the formal equation

    U(q) = sum_{j>=1} w_j q^j exp(lambda_j U(q)),

assume w_1=1, nonnegative primitive weights and slopes, and, outside a finite
prefix, w_j=1 and lambda_j=a*j^2+b*j+d with a>0. Put beta=lambda_1+w_2.
If Q is the compositional inverse, its coefficients satisfy

    [u^n] Q(u) ~ -S_n exp((b-beta)*r_n/a),
    r_n*(1+r_n)*exp(2*r_n) = a*n,
    S_n = exp(n*r_n*(1+2*r_n)/(1+r_n)) / sqrt(1+4*r_n+2*r_n^2).

The pure-model specialization proves the explicit quadratic inverse
conjecture in ProveIt's `Finite_Core_Universality_Exponential_Feedback`
article at the pinned snapshot. The manuscript also proves eventual
negativity, finite-prefix sensitivity, a positive-axis inverse Borel growth
equivalent, and a least-formal-term equivalent.

The central argument estimates all configurations with at least two actions
above a sufficiently large fixed cutoff by an arbitrarily small polynomial
multiple of S_n, before cancellation. The remaining one-action contribution
is evaluated using a finite analytic inverse core.

## Contents

- `article.pdf`: compiled 20-page manuscript, including nine further research questions.
- `article.tex`: standalone LaTeX source (no ProveIt checkout or external TeX inputs required).
- `code/verify.py`: exact finite algebra checks and floating asymptotic diagnostics.
- `data/*_exact_egf.csv`: integer-normalized coefficients V_n = n! v_n.
- `data/asymptotic_diagnostics.csv`, `data/table.tex`: diagnostic table data.
- `data/verification.json`, `data/verification_run.txt`: recorded run and check counts.
- `PROOF_STATUS.md`: proof dependencies, limits, and review targets.
- `SOURCES.md`: pinned repository provenance and primary literature.
- `BUILD_STATUS.json`: compilation and PDF inspection summary.

## Reproduce

Python 3.10 or later is needed for the code. The recorded run used Python
3.13.5 and mpmath 1.3.0 (see BUILD_STATUS.json for the actual environment).
All coefficient calculations use standard-library exact integer or rational
arithmetic; mpmath is used only for the decimal asymptotic comparisons.

```sh
python -m pip install -r requirements.txt
python code/verify.py --degree 320
make pdf
```

The supplied run passed 255 exact assertions in five models. Coefficients
were computed through degree 320 in the pure a=1 model and through degree
160 in each additional model. Numerical diagnostics are not interval
certificates and do not prove the asymptotic assertions.

`article.tex` embeds the recorded table. Re-running the script regenerates
`data/table.tex`; changing the sample degree does not automatically replace
the embedded table or update the manuscript's reported check settings.

## Status

These are mathematical proofs submitted for independent review, not a
Lean-verified development. The novelty claim is limited to the audited
repository conjecture and the extensions proved in the report, not an
exhaustive claim of priority over all literature. A finite table is not
presented as proof. The least term is not an analytic remainder theorem.
No repository files were modified or uploaded.

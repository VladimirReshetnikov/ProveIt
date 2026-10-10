# Bilinear Closure of Generalized Stieltjes Correlations

Research continuation prepared for Vladimir Reshetnikov's ProveIt project, 10 October 2026.

## Main deliverables

`article.pdf` and the self-contained `article.tex` present analytic proofs of the following.

- An all-order linear closure theorem for explicitly endpoint-regularized, circularly translated products of generalized Stieltjes functions. The highest Stieltjes order is `m+n+1`; the next order is absent. Coefficients are finite polynomials in positive integer zeta values.
- The coincident-endpoint version and an exact convergent collision expansion with a specified logarithmic polynomial counterterm.
- An ordinary, convergent log-Gamma autocorrelation expressed both by Hurwitz-zeta jets at -1 and by polylogarithm spectral derivatives at 2.
- Rational-grid traces, Dirichlet-character formulas, all parameter derivatives, and exact antiderivatives.

The central example is

    I_00(a) = gamma_1(a) + gamma_1(1-a) - pi^2/3,   0 < a < 1.

**I_00 is not an ordinary integral of two digamma functions.** It is the precisely defined finite part in the article. The article also gives equivalent absolutely convergent, subtracted integrals.

Classical Fourier and Hurwitz calculus are explicitly acknowledged. The identities are derived here as a research continuation, but comprehensive literature priority has not been established. This report does not claim to settle the manuscript's remaining S6 reduction or period-independence problems. The current S4 proof is already present upstream.

## Reproduce

Tested with Python 3.13.5, SymPy 1.14.0 and mpmath 1.3.0. Install the two requirements in a suitable Python environment, then run from this directory:

```sh
python -m pip install -r requirements.txt
make check
make pdf
```

`make pdf` requires a TeX installation with `latexmk`, pdfLaTeX, Latin Modern, AMS packages, microtype, hyperref, bookmark, fancyhdr and xurl. The article does not depend on external figures or bibliography files.

Equivalent individual commands:

```sh
python code/exact_coefficients.py --max-total 8
python code/verify_numeric.py --dps 45
python code/verify_stieltjes_pairs.py
python code/polylog_derivative_canary.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The exact generator supports configurable maximum total order up to 12. Computational cost grows with that choice. The recorded default is 8.

## Evidence

`results/exact_verification.json` records 45 ordered index pairs and 272 exact symbolic assertions. Polynomial divisibility is additionally enforced during construction. These are finite algebra checks, not a proof-assistant verification of the analytic arguments.

`results/numeric_verification.json` records 19 checks at 45 decimal digits, with largest absolute residual approximately 1.06e-44. `results/stieltjes_pair_verification.json` records three independent subtracted Stieltjes-product quadratures, with residuals from about 4e-41 to 2.4e-40. The total is 22 numerical diagnostics. These are not interval-certified error bounds or substitutes for proofs.

The derivative canary is separate. In the tested mpmath 1.3.0 environment, default order differentiation of `Re(polylog(s,i))` at s=2 disagreed with exact root-of-unity reduction by about 2.34e-12 for the first derivative at 40 working digits. Its script records a version-specific observation; future software need not reproduce that loss. The validating root-of-unity tests avoid that path.

## Package map

| Path | Purpose |
|---|---|
| `article.tex`, `article.pdf` | Self-contained research article and compiled PDF |
| `code/exact_coefficients.py` | Exact Gamma-ratio coefficient engine |
| `code/verify_numeric.py` | Independent quadrature, kernel and identity checks |
| `code/verify_stieltjes_pairs.py` | Three independently evaluated Stieltjes products |
| `code/polylog_derivative_canary.py` | Minimal numerical accuracy reproducer |
| `results/coefficients.json` | Machine-readable exact coefficient table |
| `results/identities.txt` | Human-readable identities and collision polynomials |
| `results/*verification.json` | Recorded exact and numerical results |
| `integration/07-stieltjes-correlations.tex` | Proposed namespaced manuscript section |
| `integration/standalone.tex` | Wrapper used to compile-test that section |
| `INTEGRATION.md` | Suggested repository placement, no automatic writes |
| `notes/AUDIT.md` | Review scope, finite-part cautions, computational finding |
| `notes/PROVENANCE.json` | Inspected sources and snapshot information |
| `notes/CLAIMS.json` | Claim-by-claim evidence and limitations |
| `SHA256SUMS` | Checksums of the delivered files, excluding itself |

JSON coefficient strings use `z2`, `z3`, ... for zeta values, arrays `a` and `b` for gamma_j(a) and gamma_j(1-a), and `L` for log(a) only in collision polynomials. This last convention is different from the local article notation L=log(2*pi) in the log-Gamma section.

## Integration and scope

No repository file was changed. The suggested destination is a new report under `Analysis/Polylogarithms/docs/reports/stieltjes-correlation-closure/`. Consult `INTEGRATION.md` before adding the optional manuscript section. The incoming ZIP inventory and intake instructions were inspected; the binary incoming packages were not unpacked or audited. Earlier manuscript reads were not all pinned to one Git commit; individual observed blob identifiers are recorded where available.

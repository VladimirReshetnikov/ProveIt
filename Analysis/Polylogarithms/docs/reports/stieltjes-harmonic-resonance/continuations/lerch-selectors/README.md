# Polynomial Lerch Selectors

**Endpoint obstructions, resonant spectral collapse, and Stieltjes confluence**  
Research continuation for Vladimir Reshetnikov's ProveIt project — 11 October 2026.

The main deliverables are `article.pdf` (25 pages) and the self-contained
`article.tex`. The article has complete proofs, explicit evaluations, a
version-specific source audit, and eight further research questions.

## Results and scope

The incoming *Affine Gamma Polarization* report asks for weights isolating
one polylogarithm/Lerch order and for their untwisted limit. This continuation
classifies every polynomial weight for a positive integer interval length,
a positive initial argument, and a nonzero twist in the closed unit disk.
The allowed coefficient field is C(s), with a specified finite exponential
remainder. Off resonance the weights are classical Frobenius–Euler
polynomials; at resonance they are Bernoulli polynomials plus a constant.
A proof of functional independence turns the endpoint basis statement into
an actual classification, not a claim about independence of numerical periods.

The endpoint obstruction is sharp: a nonresonant single-order polynomial
cannot vanish with its first derivative at both endpoints. An exact finite
mixture of selectors replaces the impossible scalar confluence. All removable
integer-order jets, an all-order weighted Stieltjes calculus, and anchored
shift primitives are proved. Examples include Euler-weighted log-Gamma
integrals with one odd zeta value and quartic Stieltjes/trigamma identities.

Section 11 also resolves the explicit coefficient question on page 9 of
arXiv:2609.13796v1: the coefficients are
`alpha_j = (-1)^(j-1) binomial(v-1,j)`.
It derives corrected Mellin and interpolation formulas from that paper's
Definition 1. The corrections concern the inspected version and normalization;
they are not claims that the ProveIt manuscript contains those errors.

Frobenius–Euler bases, Eulerian interlacing, and the classical Lerch expansion
are credited to prior literature. Global priority is not established.
The S6, revised S8, and general unequal-tail optimal-prefix questions remain
unresolved by this report. There is no proof-assistant formalization.

## Reproduction

Tested with Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0, and pdfLaTeX
(TeX Live 2025 development build). The scripts use only standard Python modules plus the two
packages in `requirements.txt`. From this directory:

```sh
python -m pip install -r requirements.txt
python scripts/verify_exact.py
python scripts/verify_numeric.py
python scripts/verify_coefficient_problem.py
make pdf
```

`make check` runs the three Python scripts. The numerical suite is deliberately
slower than the algebraic checks; it includes independent quadrature and order
differentiation. Every script exits with an error on a failed assertion.
`make pdf` needs a LaTeX installation with the packages named in `article.tex`.
No network access is used by the verification scripts.

Recorded results: **969 exact assertions, including six mutation controls;
33 numerical comparisons at 75 working decimal digits.** All pass. The
largest recorded scaled discrepancy is about **3.075e-36**, with a case-specific
tolerance of 1e-32 for that comparison. These are floating-point diagnostics,
not interval-certified bounds. The all-order statements rest on the proofs.
Detailed counts, discrepancies, and tolerances are in `results/*.json`.

## Package layout

- `article.tex`, `article.pdf`: complete standalone article.
- `scripts/`: exact algebra routines, exact checks, numerical diagnostics,
  and the independent coefficient-problem verification.
- `results/`: machine-readable receipts, explicit formulas, and replay logs.
- `integration/lerch_selectors_summary.tex`: optional short manuscript fragment.
- `INTEGRATION.md`: proposed placement, dependency map, and ledger entries.
- `SOURCE_AUDIT.md`, `source_manifest.json`: source provenance and correction scope.
- `BUILD_VALIDATION.json`: compilation and rendered-review receipt.
- `SHA256SUMS`: hashes of the delivered files, excluding this hash file itself.

Only new continuation files are included. External papers, predecessor sources,
fonts, build auxiliaries, and rendered review images are not redistributed.
No GitHub or persistent Library files have been edited or uploaded.

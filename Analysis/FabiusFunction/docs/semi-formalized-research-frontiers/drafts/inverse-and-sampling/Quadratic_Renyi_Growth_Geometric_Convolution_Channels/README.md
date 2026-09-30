# Quadratic Rényi Growth
## A Universal Linear Correction and Endpoint Selection in Geometric Convolution Channels

Research article prepared for Vladimir Reshetnikov, 30 September 2026.

The article answers the question **“Growth above the critical Rényi order”** in the
ProveIt draft *Beyond Polynomial Diagonals: Nuclear Bayesian Operators, Exact Null
Modes, and a Rényi Phase Transition for Fabius–Rvachev Laws* (29 September 2026).
The inspected source is pinned in `PROOF_AUDIT.md` and in Section 11 of the article.
No files in the GitHub repository were modified.

## Result

Let `0 < q < 1`, `L = log(1/q)`, and let `U_j` be independent uniform variables on
`[0,1]`. Set `X=(1-q) sum_{j>=0} q^j U_j` and let `S_m` be its first `m` terms.
For every fixed `alpha > 2`, the article proves

    I_alpha(S_m;X) = (alpha-2) L m^2 / 2 + B(alpha) m + O(log(m+1)^2),

    B(alpha) = alpha(alpha-2)/(alpha-1) log(alpha)
               - (alpha-1) log(alpha-1).

Here `I_alpha = D_alpha(P_{S_m,X} || P_{S_m} x P_X)`; it is not Sibson or Arimoto
information. Both coefficients are multiplied by `max(theta_0,theta_1)` for
Beta(theta_0,theta_1) innovations with both parameters at least one. The article
also proves endpoint selection and radial/allocation large-deviation principles
under the probability measure tilted by the Rényi integrand.

The theorem is for fixed parameters. It does not establish the joint crossover
`alpha=2+u/m`, nor does it assert a uniform error as `q` approaches one.

## Contents

- `article.pdf`: the 19-page article, including detailed proofs, provenance,
  validation boundaries, and nine further research questions.
- `article.tex`: complete LaTeX source, with embedded bibliography.
- `checks/verify.py`: exact algebra and dyadic-density checks plus optional
  floating-point endpoint quadrature.
- `checks/verification.json`: executed exact checks and point diagnostics.
- `checks/saddle_rows.tex`: generated table used by the LaTeX source.
- `checks/quadrature_24.json`, `checks/quadrature_32.json`: optional windowed
  quadrature runs, with their limits explicitly recorded.
- `requirements.txt`, `Makefile`: dependencies and rebuild commands.
- `PROOF_AUDIT.md`: proof dependencies, computational checks, and limitations.
- `SHA256SUMS`: integrity hashes for the other package files.

## Rebuild the PDF

A TeX installation providing AMS packages, New PX fonts, geometry, microtype,
mathtools, booktabs, array, longtable, xcolor, enumitem, fancyhdr, xurl, hyperref,
cleveref, and aliascnt is sufficient. No external image or bibliography files
are needed; the generated table is retained in the package.

    make pdf

Without `make`, run the following command three times in this directory:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex

## Reproduce the checks

Python 3.10 or later is recommended.

    python -m pip install -r requirements.txt
    python checks/verify.py --dps 100

This regenerates `verification.json` and `saddle_rows.tex`.
Optional runs used for the supplied diagnostics are:

    python checks/verify.py --quadrature 8 12 --nodes 24 --dps 80
    python checks/verify.py --quadrature 8 12 --nodes 32 --dps 100

The script uses exact Fraction/SymPy arithmetic for its algebraic identities and
dyadic values. Logarithms and numerical quadrature are floating-point. The
quadrature omits the middle region and truncates the radial domain; the analytic
omitted-density-term bound does not include floating-point rounding. Consequently
these estimates are **not certified values of the complete Rényi information**.

## Research and verification status

The analytic results are proved in the text. No Lean/Rocq proof, independent
peer review, or exhaustive literature-wide priority verification is claimed.
The source and PDF are the deliverable, not an automatic modification of ProveIt.

# Polynomial auxiliary scales and Kummer prime races

Start with `report.pdf` (10-page research note); `report.tex` is the complete source.

## Results

1. A compact logarithmic auxiliary-window theorem: `[t, Ct]` in place of the upstream `[t, t²]`, with exponentially large coefficients and a finite convex combination for multiple observables. Complete classical proof.
2. An averaged positive-block one-sided detector for Dedekind RH of prime-index Kummer fields for the base 2. Under Dirichlet GRH, a deficit of nonresidue primes is sufficient. Complete classical proof; the required inequality is not established.
3. A density-limit Hooley argument requiring RH only for prime-index Kummer fields, not composite squarefree-index fields, giving Artin's constant for 2 if the new inequality is proved for all odd primes. This is a conditional implication, not a proof of the primitive-root conjecture.
4. A precise source-compatible covolume target and a mean-square obstruction to substituting periodic weights.

`verify.py` is standard-library-only and checks the exact character formulas and finite product-group calculations. `checks.txt` records its executed output. Numerical gamma constants and partial Artin products are illustrative, not certified analytic estimates. `provenance.md` identifies the inspected sources, prior reports, and limitations. No Lean proof of the new results or local rebuild of the upstream proof is claimed; the mathematical proofs are in the manuscript. The research claims do not assert publication priority.

## Reproduction

Run `python3 verify.py`. Compile `report.tex` twice with `pdflatex -interaction=nonstopmode -halt-on-error report.tex`. `SHA256SUMS` hashes the delivery files (excluding itself).

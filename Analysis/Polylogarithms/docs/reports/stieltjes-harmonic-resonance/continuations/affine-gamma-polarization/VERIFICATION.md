# Verification scope

## Exact finite assertions

The checked total is 2,187:

| Script | Count | Independent objects compared |
|---|---:|---|
| `check_algebra.py` | 1,255 | Bell recurrence/exponential, canonical normal form and primitive, closed square coefficient formula, beta and hypergeometric coefficients |
| `check_endpoint_algebra.py` | 728 | Endpoint derivatives, Bernoulli residue identities, reciprocal-Pochhammer expansions and complete-harmonic recurrences |
| `check_profiles.py` | 75 | Direct profile Bell expansion and canonical reduction versus the proposed symbol formula |
| `check_selectors.py` | 129 | Selector derivative data, inverse basis expansion, beta–Bernoulli transport, and Stieltjes residues |

The algebra checker treats monomials as sorted tuples of derivative indices,
with rational coefficients. It checks `A_m = N_m + D T_m`, functional support,
and parity through weight 18. It separately constructs 183 selected Bell
factor-degree sectors, and 234 kernel coefficient cases. `gamma_normal_forms.json`
retains full normal forms and primitive certificates through weight 14.

The tests include deliberately wrong alternatives, such as dropping a factorial
or using the wrong Bernoulli endpoint convention. Rejection of a mutation is a
finite implementation guard, not an additional all-order theorem.

## Numerical diagnostics

The four parts record 15 + 14 + 6 + 21 = 56 comparisons at 50 working decimal
digits. Errors use `abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))`.

The default threshold is `1e-30`; explicit overrides in the code handle a
quadrature-convergence comparison and a difficult endpoint comparison. The
largest recorded scaled residual, approximately `2.6134075e-29`, compares
24-node and 36-node quadratures for gamma_1. Its threshold is `1e-23`.
The finer quadrature versus the Stieltjes endpoint formula has scaled residual
approximately `5.4865e-43`, and the explicit quartic gamma_1 formula approximately
`4.2137e-40`. These are not rigorous error enclosures.

Alternative representations include beta quadrature versus 0F1; compact
Hurwitz quadrature versus finite endpoint expressions and Mellin quadrature;
ordinary polygamma quadrature versus explicit zeta values; Stieltjes quadrature
versus spectral derivatives; Lerch integrals versus polylogarithm endpoint
filters; and Bernoulli-weighted integrals versus selector formulas.

Tiny absolute values do not certify an equal number of relative digits.
No PSLQ search or numerical independence claim is used.

## Reproducibility and trust boundary

`run_all.py` executes each script, stops on failure, then writes a summary.
`--summarize-only` aggregates already present result files. The recorded checks
were executed in separate bounded tool invocations; one end-to-end invocation
hit the host's wall-clock limit during the last numerical part, which was then
rerun successfully on its own. The final summary aggregates all completed parts.
This execution detail does not change their individual assertion counts.

The all-index results are established by the article's proofs. The executable
checks are finite diagnostics and certificates, not Lean/Rocq formalizations.
The PDF was compiled and visually reviewed; a separate machine preflight checks
for unresolved references and text outside page bounds. No source archive was
silently treated as inspected merely because its filename was known.

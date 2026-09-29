# Proof status and scope

All mathematical theorems in article.tex are presented with written proofs.
This is an AI-assisted, unrefereed research manuscript. No proof assistant
was run and no formal verification is claimed.

## What is proved in the manuscript

1. Catalan first- and last-endpoint formulas.
2. A countable probability space of finite absorbing skeletons and its
   exact cost distribution and tail.
3. A deterministic reconstruction lemma and injectivity of short
   skeleton families, uniformly over suitable large holes.
4. A total-variation upper bound from a common subprobability measure.
5. Exact dependent-endpoint clipping and the algebraic deficit law.
6. Two-term point and survival asymptotics and a matching total-variation
   lower bound, establishing sharp order n^(-1/2).
7. A uniform absolute moving-bound estimate, a relative asymptotic in the
   entire unbounded sublinear deficit window, and fixed-window limits.
8. A moment transition at p=1/2, including its logarithmic coefficient,
   mean and variance orders, and the limiting moment/quantile statements.
9. An exact finite formula independently checking P(D=1)=7/48.

## Inputs

Elementary Catalan combinatorics, Lagrange inversion for the endpoint
coefficient formula, Stirling's formula, countable probability, and the
standard univariate singularity-transfer principle. Required analytic
continuation and the local expansion are checked explicitly. No fixed-m
asymptotic theorem from the repository is used as a premise.

## Exact tests (finite only)

See data/verification.json and data/symbolic_verification.json. Passing
finite tests is not a proof of the all-n, analytic, or asymptotic claims.
The code does not establish cross-cost injectivity by exhaustive testing;
the article proves it by unique parsing.

## Not claimed

- A bulk-profile equivalent when n-m is a fixed fraction of n.
- Exact leading constants for E D_n or higher supercritical moments.
- The exact total-variation asymptotic constant.
- Resolution of the fixed-bound spectral component-ordering problem.
- Minimal algebraic degree four or irreducibility of an eliminated polynomial.
- External peer review, an exhaustive novelty search, or priority certification.
- Any modification, commit, or upload to the user's GitHub repository.

# Proof-status and scope ledger

## Abstract results proved in full here

Assume X >= 1 and 1 <= X_n <= n, with
(A1) P(X>x)=a x^(-alpha)+O(x^(-alpha-beta)), alpha,a,beta>0;
(A2) sup_x |P(X_n>x)-P(X>x)|=O(n^(-alpha));
(A3) n^alpha P(X_n>nu) -> Psi(u) for every 0<u<=1.

The manuscript proves the boundedness of b(u)=Psi(u)-a u^(-alpha), a uniform
regularized complex-moment expansion, the critical constant and subcritical correction,
a two-term 1/log n exponent-window law, and a two-endpoint signed measure correction
in the dual bounded-Lipschitz norm. It also proves tilted probability limits,
logarithm-weighted critical moment expansions, an intermediate-scale counterexample
when A2 is dropped, and stability under o(n^(-alpha)) survival perturbations.

All proofs are conventional written arguments. No proof-assistant checking is claimed.

## Permutation application

Uses exactly the limiting law/tail, uniform tail error inherited from total variation,
and bulk profile in the pinned ProveIt report, as detailed in SOURCES.md.

On those inputs, the two explicit repository questions resolved are:
1. Convergence and exact constant of E sqrt(D_n) - (3/(2 sqrt(pi))) log n.
2. The first asymptotic correction to E D_n^p for every fixed 0<p<1/2.

The log-uniform critical bias, endpoint correction, tilted laws, and moving exponent
window are additional consequences proved here. They are not claimed to have been
externally refereed or certified new to the entire literature.

## Computational verification actually performed

The exact JSON output describes the checked finite ranges. Counting arithmetic uses
Python integers; PGF arithmetic uses Fraction. Symbolic identities are checked using
SymPy. The checks cover 23,713 explicitly generated avoiders, 784 endpoint-state
comparisons, the full distributions through n=64, 129 PGF coefficients, and five
algebraic identities. Direct pattern testing through n=7 independently validates
the recursive avoider generator.

The constants were computed at 40 and 70 decimal working precision with mpmath.
An independent integral checks j, and a symmetric regularized Mellin evaluation
checks h. These are numerical regressions, not rigorous interval enclosures.
Neither exact finite enumeration nor precision agreement proves the asymptotic
or analytic-limit steps in the manuscript.

## Assertions deliberately not made

- No new local limit for individual lattice probabilities.
- No exact leading constant for the original total-variation error.
- No transition law at the half-size adjacency threshold m=n/2.
- No correction theorem for p<=0, despite analytic continuation of a coefficient.
- No o(1)-accurate second-order constant for fixed supercritical p.
- No uniformity for unbounded lambda in the moving exponent window.
- No total-variation convergence from discrete biased laws to a continuous limit.
- No positive-measure interpretation of the signed B0 endpoint coefficient.
- No elementary closed form, rationality/transcendence result, or certified decimal
  enclosure for the microscopic constant.
- No formal Lean/Rocq proof, external peer review, or publication-priority claim.

## Sensitive normalization checks

a=3/sqrt(pi), but the leading critical logarithm coefficient is a/2.
c_star=h+j, B0=h-a, B1=a+j, and B0+B1=c_star.
The finite part of the meromorphic correction coefficient at p=1/2 is B1, not j.
The incomplete beta expression is regularized below p=1/2; no divergent integral
is treated as an ordinary integral. Complex powers always use the real logarithm
of a positive base.

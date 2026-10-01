# Proof status and contribution ledger

## Imported theorem

The equivalence between real stability of the incidence–apex matching-support
polynomial and a branch-complete marked hull with an ADE terminal skeleton is
imported from the pinned ProveIt report, `mts:thm:main`. The allowed finite and
affine tree shapes are imported from `mts:tab:ADE`. No new all-size analytic
proof of this classification or new formal audit of the source is claimed.

All counting statements can instead be read as self-contained theorems about
the explicitly defined combinatorial class of ADE-admissible markings.

## Ordinary mathematical proofs supplied here

- Exact skeleton generating function and labelled joint count by marks/hull size.
- Exact multivariate generating function and finite-correction Poisson identity.
- Fixed-mark asymptotics, chi hull law, uniform skeleton and Dirichlet subdivisions.
- Uniform rare-event equivalent for every sequence p*sqrt(n) -> infinity.
- Uniform sparse comparison and explicit critical-window crossover/laws.
- Fixed-density moving-pole estimate, joint Gaussian law, and constant cumulants.
- Conditional skeleton-family weights and logarithmic diameter–hull discrepancy.
- Deterministic diameter sandwich, strict annealed–quenched separation.
- Eventual-constant skeleton coefficient universality for probability/hull statistics.

## Classical ingredients, not claimed as new

Labelled tree and rooted-forest counts; the matrix-tree expansion; Prüfer codes;
Lagrange inversion; Cauchy coefficient estimates; Stirling's formula; elementary
Poisson central limits and Chernoff bounds; characteristic-function CLT transfer.
The long-path diameter large-deviation calculation is included with its proof,
not promoted as a first-priority result about random trees.

## Executed checks

See `data/verification.json` and `data/extra_checks.json` for exact counts and
bounds. All recorded tests passed. They verify finite enumeration and algebra,
not infinite-size asymptotics or the entire imported stability theorem.

## Limits that must be preserved

The Gaussian and conditioned-diameter theorems currently require fixed p in
(0,1); the probability equivalent has a wider uniform range. The critical chi
law concerns the hull, not the full host diameter. The deterministic quenched
estimate is a polynomial-factor bound, not an asymptotic equivalent. The
universality theorem for eventual-constant coefficients does not transfer the
ADE-specific geometric conclusions without extra shape hypotheses.

No Lean/Rocq verification, independent peer review, exhaustive literature
priority audit, or resolution for every random-tree model is claimed.

# Source and research-target provenance

## Pinned repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Revision: `0c973d8f5e7ef4550f4df1bf486d890037fd9f14`.

Inspected project group:
`Analysis/Transseries/docs/series-and-transseries/`.

The project README, group index, and the critical-Hahn article's research
questions and proof-dependency discussion were inspected. The entire canonical
volume and all unmerged arrivals were not audited.

The target is Research Question 4, “Endpoint exponents and logarithmic
crossover,” in:

https://github.com/VladimirReshetnikov/ProveIt/blob/0c973d8f5e7ef4550f4df1bf486d890037fd9f14/Analysis/Transseries/docs/series-and-transseries/Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex

Its upper-endpoint part asks for joint alpha-to-2 / growing-order limits,
logarithmic critical charts, and cutoff laws. The present article treats this
part for the normalized exact-tail model, including approach from either side.
It does not treat the lower alpha-to-1 endpoint.

The inspected repository index describes the recent research packages as
unmerged, not claim-by-claim reviewed, and not Lean-formalized. The present
proofs do not rely on treating those packages as certified premises.

## Prior drafts inspected in the user's Library

- `article(20260929-201315).tex`, *The Logarithmic Critical Endpoint:
  Convergent Lambert Charts, All-Order Sector Laws, and Sharp Action-Cutoff
  Corrections*. Its scope statement explicitly excludes the joint moving-
  exponent limit, while treating the fixed logarithmic endpoint.
- `Marginal_Critical_Transseries.tex`, *Marginal Critical Transseries:
  Convergent Lambert-W Charts, Universal Cutoff Corrections, and Certified
  Action Budgets*. Its conclusion names uniform endpoint crossover as a
  further task.

These scope and overlap comparisons are not an independent verification of
those drafts, nor are the drafts used as proof dependencies. They are not
redistributed in this package.

## Primary mathematical references

1. NIST Digital Library of Mathematical Functions, Eq. 25.12.12:
   https://dlmf.nist.gov/25.12.E12
   The polylogarithm expansion is used before pole cancellation. The standard
   gamma and zeta Laurent expansions and the zeta functional equation are
   used to identify removable parts and local convergence.

2. Svante Janson, *Simply generated trees, conditioned Galton-Watson trees,
   random allocations and condensation*, Probability Surveys 9 (2012),
   103–252. DOI 10.1214/11-PS188.
   https://arxiv.org/abs/1112.0510
   Example 18.29 is a fixed cubic-tail antecedent of Gaussian/extreme-value
   separation under conditioning. It is credited rather than claimed as new.
   The current article supplies its own moving-exponent local-limit proof.

The main arguments also use standard Lagrange inversion, the analytic implicit
function theorem, Cauchy estimates, Taylor's theorem, and Fourier inversion;
their model-specific applications and the required estimates are provided.

## Novelty boundary

The result is a proved model-specific continuation of an explicitly identified
research question. No exhaustive priority search, general transseries
breakthrough claim, independent peer review, Lean proof, or interval-certified
software is asserted. The finite numerical data support reproducibility, not
publication priority or correctness of an infinite-limit theorem.

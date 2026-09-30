# Sources and scope audit

Inspection date: 29 September 2026.
Public repository: https://github.com/VladimirReshetnikov/ProveIt
Inspected snapshot: `0c973d8f5e7ef4550f4df1bf486d890037fd9f14`.

## Public repository content actually inspected

1. The transseries project README:
   https://github.com/VladimirReshetnikov/ProveIt/blob/0c973d8f5e7ef4550f4df1bf486d890037fd9f14/Analysis/Transseries/README.md
2. Opening 140 source lines of the series-and-transseries group index,
   plus the relevant directory/package inventory:
   https://github.com/VladimirReshetnikov/ProveIt/blob/0c973d8f5e7ef4550f4df1bf486d890037fd9f14/Analysis/Transseries/docs/series-and-transseries/README.md
3. Complete README of the fixed-stable companion package:
   https://github.com/VladimirReshetnikov/ProveIt/blob/0c973d8f5e7ef4550f4df1bf486d890037fd9f14/Analysis/Transseries/docs/series-and-transseries/Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/README.md

These sources establish the neighboring project's scope and proof boundaries.
This was not a line-by-line audit of the canonical volume, all incoming
manuscripts, or all Lean sources. No repository theorem was used as an
unverified premise of the new proofs. Repository contents were not modified.

## Private companion and the chosen question

The user's Library file `Marginal_Critical_Transseries.tex`, titled
*Marginal Critical Transseries: Convergent Lambert–W Charts, Universal Cutoff
Corrections, and Certified Action Budgets*, was inspected through its abstract,
main-result summary, and relevant further-research section. Its first further
question explicitly asks for the joint endpoint regime (2-alpha) log n bounded,
a uniform inverse/coefficient expansion, and an interpolating prefix-independent
cutoff correction. The present article targets that question and checks its
epsilon=0 specialization against the earlier displayed formula. The private
companion is not reproduced in this package and is not a proof premise.

## Primary mathematical literature

- NIST Digital Library of Mathematical Functions, Section 25.12,
  especially equation 25.12.12:
  https://dlmf.nist.gov/25.12
  Used for the convergent polylogarithm expansion. Endpoint pole cancellation
  and all parameter-uniform estimates are developed in the article.
- Svante Janson, *Simply generated trees, conditioned Galton–Watson trees,
  random allocations and condensation*, Probability Surveys 9 (2012), 103–252.
  DOI: 10.1214/11-PS188.
  https://arxiv.org/abs/1112.0510
  Theorem 17.14, its proof, and Example 18.29 were inspected in the author's
  HTML preprint. They supply established fixed-exponent and endpoint context,
  not the new moving-index correction as a black-box theorem.
- Arijit Chakrabarty and Gennady Samorodnitsky, *Understanding heavy tails in
  a bounded world or, is a truncated heavy tail heavy or not?*, Stochastic
  Models 28 (2012), no. 1, 109–143.
  DOI: 10.1080/15326349.2012.646551.
  https://arxiv.org/abs/1001.3218
  Publisher metadata and abstract were inspected for the established
  hard/soft truncation context. No uninspected theorem from it is used.

## Priority and evidence

The literature search was targeted, not exhaustive. The article does not
claim that its formulas have certified worldwide priority. It distinguishes
newly supplied conventional proofs, credited classical identities, exact
finite symbolic checks, numerical diagnostics, and future formalization work.
The research claim is restricted to the admissible analytic finite-prefix,
eventually exact power-tail family and the bounded moving-index window.

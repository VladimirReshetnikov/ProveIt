# Source provenance and scope

Date: 29 September 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned tree: `db68f0853c3c69cd930caedab6f6ad9addb11eaf`

Focused inspection included the `Analysis/Transseries` tree, the group README
at `Analysis/Transseries/docs/series-and-transseries/README.md`, and the README
of `Critical_Transseries_Moving_Fold` beneath that group. Repository content
was accessed through the connected GitHub tool. This was not a complete
line-by-line audit of the canonical volume or the Lean corpus.

## Preceding Library article

Title: *Beyond Finite-Action Folds: Critical Hahn Transseries, Stable Sector
Asymptotics, and Sharp Action Budgets*.

Date: 29 September 2026. Editable Library source:
`article(20260929-193550).tex`.

The model, principal result statements, and Section 11 research questions
were inspected. Question 4 requests endpoint logarithmic charts and cutoff
laws. Questions 1, 2 and 7 concern slowly varying tails, quantitative cutoff
errors and higher-order finite-fold drift. The present article gives defined
extensions in those directions; it does not settle all clauses of those
broader questions. Inclusion of this Library article in the pinned repository
snapshot is not assumed.

## Primary external sources

1. NIST DLMF, Section 25.12, Polylogarithms:
   https://dlmf.nist.gov/25.12
2. NIST DLMF, Section 4.13, Lambert W:
   https://dlmf.nist.gov/4.13
3. P. Flajolet and R. Sedgewick, *Analytic Combinatorics*, 2009;
   author-maintained book site https://ac.cs.princeton.edu/home/
4. S. Janson, *Simply generated trees, conditioned Galton–Watson trees,
   random allocations and condensation*, Probability Surveys 9 (2012),
   103–252, doi:10.1214/11-PS188; arXiv:1112.0510.
   Inspected HTML https://arxiv.org/html/1112.0510v1 includes Example 18.29
   on the cubic-tail infinite-variance Gaussian endpoint. The corresponding
   classical conditioning/extremes mechanism is not claimed as a new
   discovery in this package.
5. A. Chakrabarty and G. Samorodnitsky, *Understanding heavy tails in a
   bounded world or, is a truncated heavy tail heavy or not?*, Stochastic
   Models 28(1) (2012), 109–143; doi:10.1080/15326349.2012.646551;
   arXiv:1001.3218. Bibliographic/background comparison, not a proof dependency.

The article supplies its own mathematical arguments. Publication novelty
requires further review; absence of an exact match in the focused search is
not proof of priority. No theorem in the package is represented as newly
Lean-checked or independently peer-reviewed.

## Artifact and computation boundaries

The only modifications were to generated files in the working container.
No repository branch, commit, issue, Library source or external account was
changed. The included code does not access the network. Numerical outputs
are labeled as diagnostics and do not constitute interval certificates.

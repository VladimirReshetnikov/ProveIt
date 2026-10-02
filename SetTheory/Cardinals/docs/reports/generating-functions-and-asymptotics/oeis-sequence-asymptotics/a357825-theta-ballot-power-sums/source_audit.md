# Source and claim audit

Audit date: 1 October 2026.

## ProveIt

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected tree commit: `50f93367b2859b2727c34c68cf87684c101768cc`.

The root README and `Combinatorics/README.md` were inspected. A repository
code search for `A357825` returned no matching results. This is not an
exhaustive proof of absence, and the report does not rely on that absence.
No existing repository theorem, conjecture, or certificate is imported as
a premise. No repository files were changed.

## OEIS primary records

- https://oeis.org/A357825 — definition, sample data, November 2022 root
  asymptotic and nonconvergence observation; separate Bala supercongruence.
- https://oeis.org/A357871 — multiset definition, sample data, November 2022
  root asymptotic and nonconvergence observation.
- https://oeis.org/A357824 — common-endpoint power array and its fixed-power
  column identifications.
- https://oeis.org/A008315 — ballot triangle.
- https://oeis.org/A357825/b357825.txt and
  https://oeis.org/A357871/b357871.txt — numerical data provenance. Only
  entries n=0,...,14 are embedded for exact comparison.

The absence of a displayed proof on an OEIS entry does not establish the
absence of a proof elsewhere. The article does not describe the already
recorded nonconvergence observation as a newly discovered conjecture.

## Analytic and combinatorial literature consulted

- Miana and Romero, *Moments of Catalan Triangle Numbers*, 2020,
  https://www.intechopen.com/chapters/71899.
- Helton, Hughes, and Schlosser, *The discrete Laplace asymptotic method
  and its application to the 3XOR satisfiability problem*, arXiv:2509.16420v1,
  https://arxiv.org/html/2509.16420v1.
- NIST DLMF §§5.11, 5.15, 20.5, 20.7, for standard gamma, polygamma,
  theta-product, and theta-transformation facts.

The article does not claim to invent discrete Laplace analysis or the
Jacobi theta function. Its contribution is the concrete ballot-sum
analysis, coefficient and remainder calculations, exact envelopes,
multiset sectors, growing-power transitions, and inverse formulas.

## Search scope

Targeted public queries included `"A357825" "theta"`,
`"A357871" asymptotic`, `"ballot" "sums" "powers" "asymptotic" theta`,
and `"Catalan triangle" "growing" "powers"`.

No matching all-orders theta formula was identified in the inspected
material. This limited search does not establish universal novelty,
priority, or the current status of every related publication.

## Boundaries

Proved in the article: the stated finite-order asymptotic theorems, exact
two-endpoint estimate, bounded-shift logistic limit, fixed-sector remainders,
limiting envelopes and laws, eventual strict log-convexity, non-P-recursiveness,
and branchwise model-inverse accuracy.

Checked computationally: the finite exact assertions and numerical
consequences listed in `data/verification_status.json` and the README.

Not claimed: Lean verification, independent peer review, publication
priority, the prime-power supercongruence, all-index log-convexity,
convergence or resurgence of the complete formal expansion, or an exact
ceiling formula for all real inverse thresholds.

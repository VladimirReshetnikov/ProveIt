# Source and novelty ledger

Access date: September 29, 2026 (America/Los_Angeles).

## Repository source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit:
`1ee53d57de253d16cdaad79d1f54bbd95d76d682`

Report:
`SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders/article.tex`

Inspected report blob:
`aeadaf364b083f7e25a475bd42b777cf926769b9`

Pinned report URL:
https://github.com/VladimirReshetnikov/ProveIt/blob/1ee53d57de253d16cdaad79d1f54bbd95d76d682/SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders/article.tex

Relevant inspected portions include Part II's further-research question on
joint growth of length and adjacency bound, and Part III's scope, moment
transition, Catalan endpoints, reconstruction, and unresolved bulk/moment
questions. Part III is titled *The Largest Jump Is Almost Maximal*.

The prior report states an algebraic fixed-deficit law, a total-variation
rate of order n^(-1/2), the sublinear-deficit tail 3/sqrt(pi d), and an order
of growth for supercritical moments. It expressly leaves the mean deficit
constant and a positive equivalent for a fixed linear adjacency bound open.

This article contributes a positive bulk profile for 1/2 < m/n < 1, the
associated rare-event measure, explicit constants for every fixed p>1/2
moment, and a conditional word/split law. The elementary decompositions are
rederived; no prior probabilistic or fixed-bound spectral asymptotic theorem
is assumed in the new proofs.

## External primary sources

1. Nathaniel Nadler, *On 132-Avoiding Permutations with an Adjacency
   Constraint*, arXiv:2604.22135v1, submitted April 24, 2026.
   https://arxiv.org/abs/2604.22135v1
   https://arxiv.org/html/2604.22135v1

   Consulted for the originating adjacency problem, the maximum-position
   restriction, and the exact m=2 results. These are prior results, not
   contributions claimed by this manuscript.

2. Teruki Mayama and Dai Akita, *Finite-state enumeration of
   adjacency-constrained 132-avoiding permutations*, arXiv:2605.23519v1,
   submitted May 22, 2026.
   https://arxiv.org/abs/2605.23519v1
   https://arxiv.org/html/2605.23519v1

   Consulted for the endpoint-state recurrence, fixed-bound enumeration and
   growth theory. The recurrence used in `code/model.py` is attributed to
   this source and rederived in Appendix A; it is not presented as a new
   algorithm.

## Scope of verification and priority search

The source inspection and targeted searches locate the contribution relative
to the inspected repository and primary papers. They do not establish global
publication priority or exclude unpublished or uninspected work. No result
is claimed to have been externally refereed or proof-assistant verified.

Finite computation confirms the recorded combinatorial instances and
symbolic identities. Universal asymptotic statements depend on the written
proofs, especially the rare-event-scale tail bound and endpoint acceptance
calculation. Large-size decimal ratios are illustrations derived from exact
integer counts, not certified convergence rates.

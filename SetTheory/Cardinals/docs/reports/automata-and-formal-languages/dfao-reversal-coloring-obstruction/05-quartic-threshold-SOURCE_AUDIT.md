# Sources, scope, and provenance

Date of preparation: 28 September 2026 (Pacific date).

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `e2b1f016a94102663f12b970e6dd434229f90d01`.

Relevant directory:
`SetTheory/Cardinals/docs/reports/automata-and-formal-languages/dfao-reversal-coloring-obstruction/`.

The repository was accessed through the connected GitHub tool. Inspected
items relevant to the result include:

- the repository/report directory information and report-collection README;
- the selected report's `README.md`;
- its `code/reversal.py` implementation of collision graphs, chromatic counts,
  structural upper bounds, and the Davies lower expression;
- its `02-three-output-SOURCE_AUDIT.md`.

The last item explicitly identifies a complete three-output extension and
leaves four and more outputs for further work. The selected report's main
README records finite structural equality over 7<=n<=30 and 3<=k<n, not a
proof of the all-n optimum for arbitrary k.

These files identify the baseline. This is not a full audit of every source
file, report, formal theorem, or incoming package in ProveIt. No Lean build
was run and no formal status is inherited from the repository.

## Primary published source

Sylvie Davies, *State Complexity of Reversals of Deterministic Finite Automata
with Output*, arXiv:1705.07150v2, 17 October 2017.

- https://arxiv.org/abs/1705.07150
- https://arxiv.org/html/1705.07150v2
- https://arxiv.org/pdf/1705.07150v2

Inspected points: the coloring-orbit formulation (Proposition 4), Theorem 3,
Corollary 3, the k>=4 period contribution, the output-map existence lemma,
and the concluding optimality question (Problem 2). PDF printed pages 12
and 17 were also inspected as page images. The operative imported result is
the coprime-cycle lower-bound construction, not an assumption of the
conjectured optimum.

The published statement supplies an accessible (trim) witness. The article
separately verifies original-state minimality by proving/checking that the
attained reverse complexity exceeds k^(n-1).

## Background reference

Markus Holzer and Barbara König, *On deterministic finite automata and syntactic
monoid size*, Theoretical Computer Science 327(3), 319-347 (2004).
DOI: https://doi.org/10.1016/j.tcs.2004.04.010

The bibliographic record was checked. This is background for the k=n
transformation-monoid connection, not a separately imported uninspected proof.
The lower-bound dependency is explicitly cited through Davies.

## Literature-search boundary

Searches included the exact Davies title and combinations of DFAO, reversal,
optimality, three/four outputs, and recent-year terms. Broad acronym searches
returned many unrelated results, which were not used as mathematical evidence.
No later complete solution was located in the inspected search results.

This limited search is not an exhaustive citation-index review, a survey of
unpublished manuscripts, or correspondence with specialists. It cannot
establish historical priority. The extension claims are relative to the
explicit boundary of the inspected primary and repository sources.

## Novelty boundary

The collision graph mechanism, the orbit formulation, and the published lower
construction are antecedents. The additional results developed in this
package are the all-k effective eventual comparison, the uniform quartic
threshold, the four finite-slice closures, the corresponding k>=4 extremizer
constraints, and the matching/asymptotic consequences stated in the article.
Standard background identities are proved or explained rather than advertised
as newly invented mathematics.

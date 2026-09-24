# Source provenance and scope

Consultation date: 19 September 2026.

## OEIS conjecture

**OEIS A391632**, “Number of mutual-visibility sets in the n-Andrásfai graph.”
https://oeis.org/A391632

The entry attributes its conjectured rational generating function to Andrew
Howroyd, 12 January 2026. The author line attributes the sequence entry to
Eric W. Weisstein, 14 December 2025. It displays 15 terms. The formula remained
explicitly labeled “Conjectured g.f.” at the time of consultation. The first
15 values in `code/verify.py` transcribe those displayed values; the independently
computed sequence agrees with all of them.

No proof was present in that entry when consulted. Exact sequence-identifier and
graph/visibility keyword searches did not locate an earlier proof. Several search
results were irrelevant, so this is not an exhaustive bibliographic exclusion.
The report makes no claim that every refinement is previously unpublished.

## Definition of mutual visibility

Gabriele Di Stefano, *Mutual Visibility in Graphs*, arXiv:2105.02722,
version 2, 15 July 2021.
https://arxiv.org/abs/2105.02722

This is the original research source used for the existential shortest-path
condition. The article's proof distinguishes mutual visibility from the stronger
condition that all shortest paths avoid other selected vertices.

## Graph convention

Ali Behtoei, Shiroyeh Payrovi, and S. Batool Pejman,
*Metric dimension of Andrasfai graphs*, arXiv:1706.06852, 21 June 2017.
https://arxiv.org/abs/1706.06852
https://arxiv.org/html/1706.06852v1

The introduction explicitly defines the graph as the Cayley graph on Z/(3k−1)Z
with connection set {1,4,7,...,3k−2}. This fixes the graph indexing and adjacency
convention used in the report. The present report independently proves the exact
common-neighbor formula and the resulting diameter-two property.

## Separation of source facts and derived results

The source facts are the graph convention, the visibility definition, the OEIS
values, and the attributed conjecture. The flag recurrence, its circular
uniqueness proof, the four-state trace formula, the bivariate function, the block
and fixed-deficit formulas, and the stated asymptotic/probabilistic consequences
are derived in the accompanying report. They are not being attributed to the
three sources above. The package has not been submitted to OEIS or another public
repository by this workflow.

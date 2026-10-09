# Research status and claim ledger

## Proved in the article

1. Five-height cocycle transport preserves the integral class through a checked legal formal bipyramid.
2. For belt heights x <= y <= z and apices L <= U, the 2–3 Euler jump is -2 max(L-z,0) - 2 max(x-U,0). The normal-piece jump has the displayed nonnegative min/max formula.
3. A 3–2 epoch terminates after fewer than its initial tetrahedron count, with no increase in edge max-norm. The complexity statement includes the actual cost of normalizing arbitrary initial offsets.
4. After u upward moves, edge magnitudes are at most 2^u times their initial bound. Normalized coordinate bit length grows by at most u.
5. Deleting p distinct marks from a raw degree-two interval multigraph creates at most k+2p interval rows. Every noncircular residual component has exactly two distinct endpoint occurrences.
6. Four additive coordinates decode those endpoint pairs exactly. The encoding has O(log N + log p) bit values, with O(p) initial weight runs.
7. Vertex-link multiplicities are nondecreasing and peeled piece count is nonincreasing under coherent 3–2 transport, excluding global regauging and gcd division.
8. Thirteen least corner records per global vertex suffice to evaluate exact vertex-link-peeled scores at all current candidate collapses in linear total arithmetic work after preparation. This lemma has no implementation in this delivery.

## Implemented and independently replayed

- Cocycle move producer, independent checker, linear candidate scanner, deterministic first/score descent.
- Source-bound optional positive search and independent diagram-to-disc consumer.
- Marked boundary ordering with exact gaps, stable occurrence identities, direction selection, and untouched cycle multiplicities.
- Four-moment and one-hot query modes; separate residual-graph, weight, trace, and output verification.
- Callback exception preservation, shared work limits, strict integer encoding, malformed-proof rejection.

These are Python implementations. Some low-level geometry and integer routines are shared trusted dependencies; this is not a proof-assistant development.

## Measured

- A paired identical-output speedup for all-candidate scoring on the specified one-vertex family.
- A paired identical-output and identical-trace speedup for marked-boundary replay when marks are numerous.
- Correct compressed behavior on a 20,019-bit represented boundary size.
- No coverage gain in the 82-diagram corpus.
- Neutral score ordering on that corpus and small-input timing regressions.
- A checked connectivity counterexample, including full component censuses.

The final tables use reruns after callback corrections. Earlier observations are preserved with explicit provenance rather than relabeled as final-source timings.

## Conditional

A deterministic downward closure interspersed with O(log n) upward choices yields a quasi-polynomial search bound only for inputs having a successful witness in that particular family. Allowing finite upward bursts increases the branching factor by at most two per upward choice. Both formulations still need a coverage theorem and complete supplied-state disc queries.

A logarithmic upward budget alone does not bound the branching among arbitrary downward choices.

## Not supplied or not proved

- A complete general quasi-polynomial unknot recognition algorithm.
- An implemented exhaustive macrosearch.
- A full three-dimensional cutter or parallelity-bundle attachment compiler.
- Discovery or transport of all horizontal-side and peripheral labels.
- Preservation of fibre isotopy or connectivity under cocycle reselection.
- Recovery of arbitrary incidence multisets from two moments.
- A uniform end-to-end speedup of the maintained recognizer.
- A priority claim for the established annulus surgery or deletion-and-AHT ordering method.

The twelve research questions in the article focus on these remaining obligations.

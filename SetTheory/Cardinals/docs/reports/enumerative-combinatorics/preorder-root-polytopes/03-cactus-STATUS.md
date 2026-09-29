# Research and verification status

## Proven mathematically in this manuscript

The main statements have complete ordinary proofs in the text, with hypotheses
spelled out for finite simple bipartite graphs, unit edge phases, all square
minors, and vertex-indexed Hermitian diagonal pencils. The main classification,
finite-field result, gauge count, minimax theorems, and unbounded-minor-order
result do not assume an unproved repository theorem.

The stability proof of K_{2,3} imports Brändén's published multiaffine Rayleigh
criterion. The preorder consequences import the repository's height-two
matching-support transform; they are not premises of the graph theorems.

## Prior work not claimed anew

The cactus sixth-root construction, its determinant factorization, and cactus
stability are in the pinned repository report. Univariate cactus real-rootedness
is also in Ohsugi–Tsuchiya. The height-two preorder transform is a repository
result. The binary/forest observation and the general phenomenon of stability
without determinant representations are not claimed as new discoveries.

## Priority limits

This resolves a specific question explicitly asked in the pinned repository.
The source audit is targeted, not exhaustive. No claim of worldwide publication
priority is made for the classification, finite-field reformulations, gauge
count, quantitative refinements, or specific stability formulations. Possible
connections to older fundamental-transversal-matroid characterizations deserve
further literature review.

## Computational status

The supplied standard-library Python verifier was actually executed, and its
exact finite checks all passed. There is no Lean, Rocq, Isabelle, or other
proof-assistant verification. Exhaustive sixth-root checks do not substitute
for the arbitrary-complex-phase necessity proof.

## Important nonclaims

- No general characterization of real-stable or real-rooted matching-support
  polynomials.
- No nonexistence theorem for arbitrary larger determinantal pencils,
  auxiliary variables, sums of determinants, or powers.
- No solution of general preorder gamma positivity or existential flag
  realization questions.
- No extension of the sharp defect theorem to non-unit edge magnitudes.
- No claim that d(Theta(3,3,3)) equals the lower bound 3/5.
- No fixed-size minor test; the article proves such a test cannot work.
- No exhaustive survey of the complete ProveIt repository.

## Suggested independent proof audit

1. The induced-theta lemma, including a permitted length-one path.
2. The augmented-minor Schur identity and its matching bijection.
3. The three normalized core matrices and the Hermitian coefficient recovery.
4. The short-arc argument in the K_{2,3} minimax proof.
5. The convex/concave corner bounds and the rank-two Gram identity.
6. All three Rayleigh sums of squares and the leaf-stability proof.
7. The distinction between matchable vertex sets and individual matchings.

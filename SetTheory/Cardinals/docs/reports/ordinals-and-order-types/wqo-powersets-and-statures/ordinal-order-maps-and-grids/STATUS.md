# Research status and claim ledger

Date: 19 September 2026.

## Motivating open direction

Section 6 of Abriola et al., arXiv:2312.14587v2, asks how to extend its family
of elementary well-quasi-orders while retaining computability of ordinal
invariants. The source poses a broad direction. It does **not** explicitly
state the ordinal–finite grid problem in the exact form used in this article.
That concrete subproblem is selected here as an attack on the direction.

## Results with proofs in the manuscript

1. The finitary Hoare quotient of alpha x P is Mon(P^op,1+alpha).
2. For every ordinal delta and finite n-element Q,
   o(Mon(Q,omega^delta)) = omega^(natural sum of n copies of delta).
3. A finite Cantor-block formula computes o(Mon(Q,beta)) for every ordinal beta.
4. The point rank of an isotone map is the natural sum of its coordinates.
5. Exact successor and limit formulas compute the height.
6. A fork/dual-fork example, and an infinite star family, separate powerset
   profiles despite equality of all ordinary finite order-map counts and
   equality of the underlying grids' maximal type, height, and width.
7. The ordered-fiber signature is a complete invariant for the ordinal
   maximal-order-type profile at a fixed finite size.
8. One explicit probe ordinal below omega^omega recovers the signature.
9. Direct enumeration and ideal-chain dynamic programming evaluate the formula.

The proofs depend on the established maximal-linearization theorem and the
Cartesian-product/disjoint-union formulas for maximal order type. The proof
of the monomial theorem explicitly constructs a linear extension; it does
not use a general maximal-order-type formula for lexicographic products.

## Claims not made

- No complete resolution of the motivating paper's general extension program.
- No general ordinal-width formula for the map spaces or their powersets.
- No closure result for arbitrary iterations of powersets, words, and multisets.
- No intrinsic replacement for weakened invariants on all wqos.
- No proof that the ordered-fiber signature determines a finite poset up to
  isomorphism, or that the universal probe is minimal.
- No computable notation system for all countable or uncountable ordinals.
- No priority claim. Targeted searching did not establish earlier occurrence
  of the exact package of results, but absence from those searches is not a
  proof that the results are new.
- No Lean formalization or independent peer review.

## Confidence and testing

The manuscript gives conventional proofs rather than numerical conjectures.
The most important audit points are listed in Appendix B: mixed-exponent
splitting, fiber-order compatibility, minimal equal-value coordinate choice
in the rank argument, ordinal addition orientation, and finite-poset duality.

The passing finite and symbolic tests support the implementation. They do
not establish transfinite assertions. Recorded finite-poset counts use
naturally labeled transitive relations, not isomorphism classes or arbitrary
labelings.

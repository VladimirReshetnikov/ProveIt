# Independent mathematical proof review

**Date:** 9 October 2026  
**Scope:** Independent review of the article `article/planar_sector_overlays.tex` and the supplied `sector_planar.py`, `sector_planar_verify.py`, and `sector_planar_certificate.py` implementations. This note records an English proof and source-code review. It is not a Lean formalization, machine-checked proof, exhaustive literature-priority search, or a substitute for the separate computational validation.

## Main conclusion

The reviewed arguments establish the stated supplied-sector results under their explicit hypotheses: finite standard normal coordinates on a compact triangulated three-manifold, a compatible quadrilateral sector, and matching nullity at most three for the implemented branch. No remaining substantive mathematical gap was found in the planar interaction bound, the degeneracy arguments, the effective-dimension proposition, or the justification for filtering primitive extreme rays by Euler characteristic.

## Specific independent checks

1. **Canonical faces and link factors.** Canonical minimum subtraction is linear on each anchored minimum cell. Setting a triangle coordinate to zero at every global vertex defines a coordinate face of the full standard sector cone. Projection and canonical lifting are inverse on this face. Singleton vertex groups must be included conceptually when choosing anchors, even though the compiler omits their free link coordinates. This removes every pure-link direction before taking the projective section.

2. **Discarded and coincident forms.** After identical restricted affine forms are identified, full-dimensional minimizing cells cover the section by continuity from strict-minimum interior points. An affine gap nonnegative on a relative-open subdivision face cannot vanish at one interior point without vanishing throughout that face's affine hull. Thus a form attaining the minimum only on an edge or at a point introduces no missing subdivision vertex. Its triangle coordinate remains part of the reconstructed output.

3. **One-diagram size.** For a polygon subdivided into `f` convex minimum cells, let `I` count interior vertices, `B` count new boundary vertices, and `e` count interior edges. Euler gives `e = I + f - 1`; incidence counting gives `2e >= 3I + B`. Edges meeting original polygon corners contribute additional nonnegative incidences. Therefore `I + B <= 2(f - 1)` and `e <= 3(f - 1)`, including these boundary degeneracies.

4. **Exact pairwise crossing bound.** In general position, the overlay of two convex minimum diagrams satisfies `F = f_1 + f_2 - 1 + X`. Each overlay cell is a connected convex intersection of two cells, so `F <= f_1 f_2` and `X <= (f_1 - 1)(f_2 - 1)`. To remove general position, retain only full-dimensional pieces and select a strict interior witness for each. Small coefficient perturbations preserve all witnesses. Every original proper crossing has exactly two locally minimal retained pieces in each group; their transverse equality-line intersection and strict gaps persist in a sufficiently small neighborhood. Finitely many disjoint neighborhoods preserve distinct crossings under a generic rational perturbation. This proves the same inequality in degenerate inputs.

5. **Complete interaction count.** Every common-subdivision vertex is an original polygon corner, an individual-diagram vertex, or a proper crossing between open edges of different groups. Collinear overlaps contribute only existing endpoints. Consequently, with `A_v = f_v - 1` and `A = sum A_v`, the number of non-link rays satisfies `R <= b + 2A + sum_{u<v} A_u A_v <= b + A(A+3)/2`. The inherited cycle count gives `A <= p-g <= 3k+3` at nullity three. With one varying group, the interaction term vanishes and the stated linear bound follows.

6. **Sharpness construction.** Parallel strips in pairwise nonparallel rational directions attain the interaction count. The polygon must contain the origin in its interior; sufficiently small generic rational offsets put every cross-group intersection inside it. The affine functions `h_j(z) = -j z + sum_{s=1}^j tau_s` have their successive changes at the increasing offsets `tau_j`. The explicit two-group grid has `(m+2)(n+2)` vertices. This proves sharpness for abstract rational potential systems, not for realizable normal matching systems of triangulated three-manifolds.

7. **Effective dimension after recompilation.** Delete exactly the quadrilateral coordinates identically zero on the feasible cone. This changes no feasible standard normal vector. Exact cycle compilation and canonical lifting identify the rebuilt nonnegative kernel with the projection of that unchanged cone. Summing one positive feasible witness for each surviving coordinate produces a vector strictly positive on the surviving support. Small perturbations in every direction of the rebuilt kernel remain nonnegative, so that kernel equals the span of its feasible cone. The empty surviving support also satisfies the claim. The proposition is mathematical; the forced-zero feasibility preprocessor is not implemented in this delivery.

8. **Independent tie reconstruction.** The verifier intersects each nonconstant affine equality line with all coordinate and minimum inequalities by exact one-dimensional interval bounds. A nonempty positive-length interior tie is a maximal genuine ridge: a third affine gap cannot change its active status at an isolated interior point. A singleton tie has an additional independent active constraint and is a diagram vertex. Boundary ties add existing endpoints. This reconstructs the same vertex set without importing clipping, the producer's chart, or its contracted graph.

9. **Primitive lifting, connectedness, and Euler filtering.** Integer graph potentials make the canonical lift of an integer quadrilateral vector integral. Divisibility of all quadrilateral entries implies the same divisibility of all canonical triangle entries, so primitive quadrilateral normalization is valid. If a primitive integral extreme-ray surface were disconnected, each component vector would be a positive scalar multiple of the whole vector. Bezout's identity makes that scalar integral, contradicting its lying strictly between zero and one. Thus the primitive output is connected, and nonpositive Euler characteristic safely excludes a disc component. Positive Euler characteristic still requires the independent essential-disc test.

10. **Encoded coordinate bounds.** The incidence triangle block is totally unimodular, and each allowed quadrilateral column has absolute column sum at most four. Mixed-minor expansion, followed by cofactors on an independent family of supported rows, justifies the inherited `4^s` triangle and `4^(s-1)` quadrilateral bounds. These bounds concern binary encoding, not an expansion into elementary normal pieces.

## Implementation and complexity qualifications

- The producer's bounded chart, closed rational clipping, removal of zero-area cells, preprojected lifting, and native coordinate checks agree with the mathematical construction. Skipping segment pairs sharing a group is safe: two edges of one minimum subdivision cannot create an unlisted proper crossing.
- The independent checker first projects all uncontracted triangle potentials. This costs `O(tk)` arithmetic operations before deduplication. Its subsequent planar geometric construction costs `O(k^3)` before output bookkeeping; dense elimination is a separate charge.
- The arithmetic enumeration bound should include constant work, as `O(1 + k^3 + (t+k)R)`, or state `k >= 1` and treat the empty sector separately.
- Deterministic collection, sorting, and merging of constant-dimensional rational geometric records preserve the stated cubic arithmetic bound. The supplied Python implementation uses exact dictionaries and sets. A set of `Theta(k^2)` points can suffer quadratic-in-set-size collision work, so the exact cubic worst-case bound is not a proved hash-table bound for unchanged Python code. Polynomial worst-case bit complexity remains valid. Final sorting of length-`k` quadrilateral vectors is output bookkeeping and should be charged separately from planar predicates.
- Resource interruptions do not certify completeness. The source-bound checker deliberately shares the native triangulation parser and the older dense matching model; its independence concerns the enumeration construction and projected chart, not every dependency.

## Attribution and limits

Canonical extension is established normal-surface theory. The all-dimensional coordinate-face correspondence, contracted cycle count, and coordinate-height bound are inherited from the preceding project work and its cited sources. Convex minimum diagrams and normal-fan overlays also have established computational-geometric ancestry. This continuation contributes the stated planar specialization and interaction-sensitive sector bounds, their one-vertex consequence, the concrete exact branch, and its independent reconstruction-based checker relative to the audited project state.

The review does not establish realization of the sharp abstract examples by three-manifold triangulations, an output-polynomial solution of unrestricted quadrilateral-to-standard conversion, or a complete quasi-polynomial unknot recognizer. The latter remains conditional on the article's explicit sector-coverage, provenance, and testing hypotheses. Benchmark numbers, experimental coverage, and package integrity are documented by their separate generated records.

## Additional review: one-LP support extraction

The later maximal-support corollary was independently checked. For the
unnormalized cone, maximizing the sum of bounded auxiliaries `0 <= z <= 1`,
`z <= q`, `Aq = 0`, `q >= 0` has optimum equal to the number of coordinates
that can be positive. Scaling and summing positive witnesses gives the
indicator optimum; every optimum has that same indicator. The proposed
dual signs are correct. Its optimum provides a multiplier `y` with
`A^T y = 0` on the active support and `A^T y >= 1` elsewhere. Combined with
a feasible `q` positive on the proposed support, this is an independently
checkable certificate of the entire possible support. The proof must use
the homogeneous cone: imposing sum(q) = 1 or an arbitrary coordinate cap
would invalidate the scaling argument. This is a standard maximal-support
LP mechanism specialized to the sector, without a priority claim or an
implementation claim.

## Additional algebraic review: canonical Euler convexity

A separate follow-up review confirmed that any linear functional nonnegative
on the vertex links is convex after canonical extension: its formula is a
linear term minus nonnegative multiples of minima of linear potentials.
Consequently its maximum on the normalized quadrilateral section equals
its maximum at the original section corners, and these canonical corner
lifts are standard extreme rays. Euler characteristic satisfies the sign
hypothesis for compact finite manifold triangulations. A connected essential
normal disc has no vertex-link component and is canonical, so a nonpositive
corner maximum excludes such a disc in the supplied sector. Positive Euler
characteristic still requires the essentiality test. The separate executable
audit checks normalized, rather than unnormalized primitive, Euler maxima.
The new precheck remains a proposed optimization; no measured runtime is
attributed to it.

# Proof audit and critical hypotheses

## Main assumptions

C is a pointed, full-dimensional rational polyhedral cone of dimension d >= 1. A face includes {0} and C. M = C intersect Q^d. All ring elements have finite support. k is a field and D is a unital subring. “Geometric monomial ideal” means a coefficient-full direct sum of positive homogeneous k-spaces, contained in the zero-constant tail.

For the arithmetic-module dichotomy, D is additionally a PID that is not a field. For surreal realization, use (D,k)=(Z,R); for Gaussian realization, use (Z[i],C). No positive-characteristic field is embedded in No.

## Principal obligations

1. **Small shifts and coefficient mismatch.** The proof uses one shift smaller than all finitely many support constraints. Every cofactor has nonzero degree, so its coefficient can be in k rather than D. The degree-zero component is never silently changed from D to k.
2. **Flat ideals really are flat.** J_F is an increasing union of free rank-one ideals. Multiplication identifies J_F tensor J_G with J_(F join G) because flatness preserves the injection J_F -> A.
3. **Not projective.** A positive functional proves failure of finite generation. The dual-basis argument proves that any projective ideal in a domain is finitely generated. The countable telescope then gives projective dimension exactly one for J_F.
4. **Radical ideal classification.** Radicality makes membership constant on each relative interior and upward in the face poset. The converse is an intersection of prime face ideals. Arithmetic constant ideals are excluded explicitly.
5. **Exact incidence resolution.** At each positive exponent, the complex is an augmented simplex on the active generators; at degree zero it is D -> D. This proves exactness, not merely that the differential squares to zero.
6. **Legal scalar cancellation.** A nonzero scalar of k is an invertible A-linear endomorphism of J_G, even if it is not in D. Schur corrections preserve decreasing labels. Eliminating a label cannot change another diagonal block's homology.
7. **Correct homological shifts.** A subset of cardinality p is in degree p; its ordinary simplicial degree is p-1; relative-to-reduced homology adds another shift. Thus the formula uses reduced H_(p-2), including H_(-1) for one generator.
8. **Actual Tor witnesses.** The detector is an A-module via projection to a face and extension of constants to k. For H outside G, support vanishes; for H properly inside G, a cap equality kills the component; for H=G, late transitions are the identity on k. This produces nonzero ordinary Tor, not just formal label counts.
9. **Topological simplification.** The outside-vertex complex is compared to a poset of proper faces not contained in a fixed face. The barycentric retraction and an explicit radial contraction prove the required contractibility. Missing labels do not receive spurious H_(-1) contributions.
10. **Simpliciality.** A minimal pair-join gives isolated vertices and nonzero reduced H_0. Facet normals then prove linear independence of the rays when every facet omits one.
11. **Arithmetic modules.** Scalar quotients have a two-term free resolution. Torsion-free PID modules are flat over D, allowing tensoring of the cellular resolution. The cap module is a k-vector space, so torsion modules have zero derived tensor with it; the non-torsion quotient supplies the lower bound d.
12. **Nonflat embedding.** Both coefficients of every old two-ray syzygy have zero constants. A newly admitted quotient monomial yields a relation with first coefficient 1. No finite combination of old syzygies can have that coefficient. This is meaningful even for a proper-class target because only finite relations are used.

## Claims deliberately not made

- Equality pd = h+1 for every cone quotient with h >= 2.
- An all-module upper bound for the weak or global dimension of A_D(C).
- A weak/global dimension of the full proper-class Oz or Oz[i].
- Flatness of the embedding into the ambient omnific ring.
- A theorem for unrestricted infinite Hahn supports.
- Recovery of the face lattice from an unmarked abstract ring alone.
- A machine-checked or externally refereed proof.
- Exhaustively established originality.

## Finite calculations

The recorded standard-library program passed 52,080 exact assertions. It compares diagonal and reduced-simplicial homology, performs scalar cancellation, tests all face quotients in the selected cone samples, and checks rational cap inequalities. See `verification_results.json` for counts and examples. These checks support the finite implementation and indexing; they do not prove the general infinite-ring assertions.

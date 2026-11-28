# Mathematical review checklist

This is an internal proof review, not independent peer review.

1. **Normalization:** use the lattice spanned by all columns. A basis change into that lattice divides all maximal minors by its index; the minors of the resulting generating matrix have gcd one, by an integral right inverse and Cauchy–Binet. The normalized Gram determinant is invariant.
2. **Arbitrary anisotropy:** the box cover uses the prefix minimizing `(L_1 ... L_j)^(1/(j-1))` after sorting widths. It is essential to allow normals with zero coordinates. The universal list of normals has size at most `K_r (product L_i)^(1/(r-1))`. No assumption of bounded aspect ratio enters.
3. **Short dual basis:** orthogonal projection along a shortest primitive lattice vector, with length-adjusted lifts, gives the claimed basis-product bound by induction.
4. **Isotropization:** more than half of the columns lie in the ball of radius `sqrt(2r/n)` after the Gram change of metric. When hyperplane occupancy is at most n/2, these columns span, ensuring every dual-coordinate box halfwidth is at least one. Counting indexed columns controls the determinant, including multiplicities.
5. **Construction:** short representatives of projective directions exist by pigeonhole on the quotient of a prime-field vector space by a line. The representatives have nonzero residues, and the moment-curve determinant formula ensures all maximal minors are nonzero.
6. **Exact determinant vs bounded determinant:** the lower bound for the exact column number does not follow by assuming monotonicity. The anchor basis has determinant Delta, its reduction is invertible at a suitably chosen prime, and an invertible transformation of the moment curve includes these prescribed directions. Hadamard bounds all remaining minors by Delta/2. Bertrand's postulate supplies a prime not dividing Delta for every sufficiently large Delta.
7. **Scope:** fixed rank, asymptotic orders, not sharp constants for ranks >=3. The generic restriction cannot be dropped without additional arguments. The bounded-vanishing-minor corollary concerns at most a fixed number, not exactly that number. The proof is unconditional, not a new RH theorem. No Lean proof or external refereeing has been performed.

All finite checks are exact integer arithmetic and are supplemental; their success does not constitute a proof of the asymptotic lower bound.

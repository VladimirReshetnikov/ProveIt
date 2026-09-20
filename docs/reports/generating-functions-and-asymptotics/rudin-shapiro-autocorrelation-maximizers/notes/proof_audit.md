# Logical dependencies and proof audit

## The infinite conclusion does not come from extrapolating a scan

1. Finite Laurent-polynomial identities establish complementarity and the
   scalar autocorrelation recurrence directly from the defining sequence.
2. The two matrices U and V encode a bijective address system for all odd
   lower-half shifts. Even nonzero correlations vanish. Both first and second
   state coordinates are considered, accounting for all positive shifts.
3. The symmetric convex hull K_n contains exactly the word states and their
   negatives in its generating set. At each finite stage, retained points
   are actual candidates. Every discarded candidate has a checked expression
   in the convex hull of zero and three retained points, using oriented
   determinant numerators. Central symmetry ensures zero is in the hull.
   Hence this is equality of convex hulls, not a numerical approximation.
4. A unique retained exposed vertex alone would NOT prove a unique word.
   The finite checker instead backtracks support functions, demanding a
   strict inequality between the U and V siblings at every depth. It also
   demands a strict choice between the first and second coordinates.
5. The 13 rational template matrices define a moving symmetric 26-point
   polytope P(z). At n=400 (level m=402), its 26 points coincide exactly with
   the certified retained generating list.
6. On an explicit rational rectangle B, all 26 transitions are checked:
   13 exact matrix identities and 13 tetrahedral containment certificates.
   Cramer's-rule determinants are polynomials of degree at most three in
   the projective coordinates. Exact rational interval bounds certify their
   signs throughout the entire rectangle, including all boundaries.
7. All first/second template coordinates except the distinguished second
   coordinate have absolute value strictly below 1, with a uniform gap
   greater than 7/50. Therefore the only possible extremal vectors in P(z)
   are z and -z, only in the second coordinate.
8. Exact rational affine inequalities prove that J^6 maps an inner rectangle
   R into itself and J^j maps R into B for j=0,...,5, where J=-U. Positive
   denominators justify every projective cross-multiplication. The exact
   orbit U^400 v is inside R. This establishes B-membership for every future
   reference orbit point without a floating-point eigenvector argument.
9. Homogeneity and symmetry transport K_n subset P(z_n) inductively.
   im(V) is the plane x+y=0, while each distinguished vector lies outside it.
   Thus a maximizing word must begin with U. det(U)=-4 gives a unique
   predecessor. Descending to n=400 and using finite word uniqueness proves
   uniqueness for all later levels.
10. The finite checks cover m=3,...,402 and identify 39 as the last exception;
    the induction covers every m>=402. Together they establish the stated
    sharp threshold 40 and the complete exception list.

## Exact certificate counts

* 400 finite compression stages, levels 3 through 402.
* 11,016 finite tetrahedron witnesses.
* At most 70 retained points at a finite stage; 26 at the induction entry.
* 13 parametric matrix identities and 13 parametric tetrahedron transitions.
* 2,032 direct scalar-recurrence comparisons against defining sums through m=10.
* Six test methods, including small defining sums, determinant-polynomial
  checks, tetrahedron acceptance/rejection and evaluations at m=1000.

## Trust boundary

Proof verification imports only the Python standard library, uses integers
and fractions.Fraction, and has no NumPy/SciPy/SymPy dependency. The area replay
uses Python's seeded pseudorandom generator. Every proof inequality is checked
with a `require` function that raises on failure, not a Python `assert` that
could disappear under optimization. The discovery scripts may use assertions,
floating-point geometry and SymPy; none is trusted by the verifier.

The checker reconstructs template matrices from the fixed words. It does not
trust template_matrices.json for proof. Recorded finite maxima are compared
with independently recomputed maxima. The essential proof inputs are the
finite and parametric certificate JSON files. Their format and construction
are explained in the article.

## Manual audit priorities

The four most important human-review points are the address bijection;
uniqueness despite convex-hull compression; orientation and denominator signs
in the tetrahedral/projective arguments; and the n=m-2 indexing convention.
The arbitrary-scalar homogeneity argument uses central symmetry and hence
remains valid when the reference orbit changes sign.

The proof is proposed, not proof-assistant-certified. Successful execution is
strong reproducible evidence for its finite assertions but does not constitute
independent mathematical review of the reduction, induction or checker.

# Independent review of the balanced Gram recombination

## Reviewed object

`research/gram_output/balanced/equation.json`, bound by its exact source hash to the newly generated `nonunit/shared240_balanced/equation.json`. The reviewer did not alter the Gram source, search program, or output. The separately authored `review_gram.py` imports no construction or existing Gram-checker module.

## Mathematical conclusion

The final polynomial is

    Q(z) = sum_i r_i(z)^2 + sum_(i,j,epsilon) epsilon*r_i(z)*r_j(z),

where all 177 residuals are unchanged and there are 13 listed signed cross terms. Let H have diagonal 2 and the listed signs in the symmetric off-diagonal positions. Then Q=r^T H r/2 exactly.

The graph of the actual cross terms has two nontrivial components, with five and eight vertices. The other 164 vertices are isolated. The certified blocks have positive exact Schur pivots:

- five-vertex block: 2, 2, 2, 1/2, 1; determinant 4;
- eight-vertex block: 2, 2, 3/2, 5/6, 4/5, 3/4, 2, 1/6; determinant 1.

Independent rational elimination reproduces these pivots. Direct exact multiplication verifies every entry of both supplied decompositions H=L D L^T, with L unit lower triangular. The isolated blocks are [2]. Thus the full H is positive definite.

It follows for every real vector z, and hence for every integer vector z, that

    Q(z)=0  iff  r_i(z)=0 for every i.

This is an exact equality of zero sets, not an approximate comparison or an inference from sampled inputs. All coefficients of Q are integers because its displayed definition has integer residuals and signed cross coefficients. If desired, the positive-definiteness proof can be expressed entirely by a positive rational weighted sum of squares and then cleared by one positive integer denominator.

The classification of the eight-dimensional matrix as a named lattice is unnecessary for this proof. No classification claim is required by this review.

## Literal checks

The independent checker:

1. authenticates the exact copied source equation and compares its entire variable and residual arrays;
2. reconstructs connected blocks from the actual edge list, checking disjointness, isolation, signs, and absence of duplicate edges;
3. calculates positive Schur pivots from the actual matrices independently of the certificate;
4. checks all supplied LDL entries and determinants;
5. collects the complete polynomial with exponent-vector arithmetic;
6. compares every coefficient to the supplied expansion;
7. checks all 240 variables occur, and recomputes exact degree, height, support, content, and coefficient L1.

The resulting measurements are 240 integer variables, 177 residuals, exact degree four, 5,803 collected monomials, height 6,404, content one, and coefficient L1 686,958. The copied sum-of-squares source has 5,477 terms, height 15,107, and coefficient L1 855,147. The Gram rewrite therefore lowers height and coefficient L1 while increasing support; it is a genuine tradeoff, not an improvement in every metric against that immediate source.

The full machine-readable receipt is `balanced.json`.

## Scope

No gap was found in the Gram transformation or its literal implementation. It composes directly with the separately proved integral projection and the source's retained arithmetic/refutation calibration. This review does not reconstruct the complete inherited C222, Pell, CRT, or object-ZFC formalization. It is an independent mathematical and implementation review within the AI-assisted workflow, not an outside human referee report.

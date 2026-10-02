# Proof and verification audit

Date: October 1, 2026. This is an internal audit accompanying the draft,
not an independent referee report.

## Foundational boundary

Conway normal form, the monomial multiplication law, and ordinary Hahn-field
arithmetic are imported classical results. All ordinary vector spaces and
quotients in the operator theorems are set-sized. Class Hamel bases are
handled separately with a set-like global well-order and set-initial-segment
recursion under Godel--Bernays class theory with global choice.

The class of finite-monomial surreal numbers is not treated as a set. Its
proper-class cosets are not incorrectly collected into an ordinary set quotient.

## Principal proof checks

1. **Full codimension (Theorem 3.2).** Eventual Vandermonde relations give
   continuum independent cosets. For exponent groups larger than continuum,
   disjoint infinite supports in distinct cosets of Z*delta supply |Gamma|
   independent cosets. The dimension formula and vector-space cardinality
   formula then give dimension(H/E) = dimension(H) = |H|. Counting alone is
   never substituted for independence.

2. **Reduced finite basis (Theorem 4.2).** The minimum leading value exists
   because a finite spanning family is given. Each nonzero pivot functional
   drops the dimension by exactly one. The final coordinate map is an
   isomorphism, which proves uniqueness. Arbitrary infinite-prefix searches
   are not claimed computable.

3. **No valuation Hamel basis (Theorem 4.4).** The chosen basis vectors have
   leading values n*delta, but are NOT assumed Hahn-summable. A countable
   nested-ball construction and a direct support proof of spherical
   completeness avoid that invalid inference.

4. **Completion (Theorems 6.1 and 6.2).** A finite polynomial can match a
   vector through a cutoff precisely when its support there is finite.
   An infinite left-finite support has order type omega and is cofinal.
   Noncyclic ordered groups have infinite bounded well-ordered supports,
   whether or not they have a least positive element.

5. **Full surreal topology (Theorem 6.4).** For a SET of pairwise nonzero
   distances, the cut {0 | distances} supplies a positive uniform separation.
   Conclusions about convergent and Cauchy nets apply to set-indexed nets.
   They are not statements about unrestricted proper-class-indexed nets.

6. **Euler localization (Theorems 8.3 and 8.4).** Dividing coefficients by
   p(gamma) does not enlarge support. The only exceptions are finitely many
   real roots. The identities p(D)G_p = G_p p(D) = I - P_res yield an inverse
   modulo E. R(X) acts by OPERATORS, not by multiplication in a quotient field.

7. **Independent classes (Theorem 8.6 and Proposition 8.7).** Clear the finitely
   many rational denominators. A relation modulo E becomes an eventual
   coefficient identity. Largest exponential growth and then factorial growth
   give contradictions. These are R(X)-linear statements, not algebraic or
   differential-algebraic independence over the ambient Hahn field.

8. **Automatic strongness (Theorem 9.1).** The exact identity
   x = x_gamma*t^gamma + (D-gamma)*z holds with support(z) inside support(x).
   It identifies the coefficient cokernel of D-gamma. An arbitrary commuting
   real-linear map must therefore act coefficientwise, without any initial
   continuity or strongness assumption.

9. **Nonsplitting (Theorem 9.3).** A commuting projection fixing all monomials
   would, by the commutant theorem, be the identity everywhere. Independently,
   a divisible submodule upstairs must lie in the image of D-gamma for every
   gamma, forcing every coefficient to be zero.

10. **Correct lift ideal (Proposition 9.5).** The kernel of coefficient
    multipliers on H/E is the ideal of reverse-well-ordered weight supports.
    The kernel is NOT limited to finitely supported weights. For Gamma = Z,
    the indicator of the negative integers has infinite support but sends
    every Laurent series to a Laurent polynomial. This distinction was
    separately checked in the internal review.

11. **Two layers (Theorem 10.1).** For noncyclic real subgroups, density supplies
    increasing gamma_n in (-1/n, -1/(n+1)). Their support is bounded, so any
    left-finite vector supported there has finite support. Polynomial values
    at gamma_n vary at most polynomially in n after factoring their order at
    zero; this permits exponential dominance. Both quotient layers have
    R(X)-dimension continuum. The upstairs nonsplitting claim is restricted
    to the case where the final quotient is nonzero.

## Edge cases and scope limits

- Gamma = {0} gives H = E = R. It is excluded from all nonzero quotient and
  infinite-dimension claims.
- The real-exponent hypothesis is essential for D(t^gamma) = gamma*t^gamma
  as an R-linear operator with distinct scalar eigenvalues. No such formula
  at arbitrary surreal exponents is imported without proof.
- Hahn sums always have set-sized well-ordered support and finite occurrence
  at every exponent. They need not be valuation limits of finite sums.
- Internal Hahn valuation topology and topology induced from the whole
  surreal line are different. Neither is a topological vector-space topology
  over R with its usual Euclidean topology.
- An independent family with continuum cardinality is not thereby a basis.
  The factorial witness explicitly disproves spanning for the geometric family.
- No explicit spanning Hamel basis, classification of all invariant subspaces,
  or all-rank Euler localization is claimed.

## Computational evidence

`code/verify.py` passed 39 exact finite checks using Python's Fraction class.
The JSON report records each check, relevant determinant values, and the
boundaries of the computation. The tests include finite row reduction,
Vandermonde determinants after finite deletions, selected exponential-polynomial
minors, Euler resonance identities, finite commutants, reweightings and shears,
and bounded-support sample identities.

The infinite proofs, class choices, dimensions, and universal statements about
all operators are NOT established by these finite tests. No proof assistant
has verified the manuscript.

## Priority audit

The classical sources and the inspected ProveIt reports are listed in the
article and `sources.json`. The normal-form, valuation, and completion
background is not claimed new. The principal operator package is presented
as a proposed contribution with complete written arguments, not as a certified
first discovery. The targeted search does not prove the absence of similar
results elsewhere in the repository or literature.

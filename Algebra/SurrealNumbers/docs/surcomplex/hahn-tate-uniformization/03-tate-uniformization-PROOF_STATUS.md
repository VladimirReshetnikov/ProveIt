# Proof status and dependency audit

## Established inputs, cited in the article

1. Hahn-field arithmetic and Neumann's positive-support lemma.
2. Universal integral Tate coordinate identities, including the cubic and
   cleared secant identities, as proved in Tate's account.
3. Conway normal-form arithmetic and its compatibility with strong summation.
4. The finite algebraic group law on a nonsingular Weierstrass cubic.

The proof does not use classical rank-one uniformization as a black box for
surjectivity. That step is proved using three formal coordinate charts.

## Written arguments supplied

- Formal evaluation at finitely many positive-valuation inputs, including
  coefficient-fiber finiteness and compatibility with composition.
- Exact summability and nonsummability domains of the raw bilateral families.
- Hahn specialization of the universal polynomial identities.
- Integral node chart, formal inverse, and factorization of the smoothing
  equation as a unit times the recovered period equation.
- Node, smooth-residue, and infinity inverses, exhausting every rational point.
- Group law via the cleared secant identities and Tate's generic-pair lemma.
- Equality of generated positive support monoids in both coordinate systems.
- Exact valuation isometry and fixed-/moving-period consequences.
- Value and residue exact sequences and the full-domain extension obstruction.
- Coherent transfer to actual No and No[i].

The proofs have been reviewed during preparation but have not undergone
independent peer review or proof-assistant verification.

## Computational checks actually run

`verify.py --degree 12` passed all eight identities, with 91 monomials per
identity and 728 coefficient equalities in total. Arithmetic is over exact
integers. Both directions of formal inverse composition are checked, as are
the cubic equation and inversion symmetries. The recorded output is included.

Finite checks do not establish the infinite or global theorems.

## Novelty boundary

Molcho and Wise already have a bounded-monodromy Tate quotient. Its one-period
valuative bounded subgroup agrees with the subgroup used in this manuscript.
The article explicitly acknowledges this precedent.

The possible contribution is the package of explicit Hahn-domain, inverse
support, and exact valuation refinements. Equivalent formulations in formal or
logarithmic geometry may exist. A complete comparison with the logarithmic
uniformization functor is a remaining priority check, not a proved claim of
this article.

## Claims deliberately not made

- No resolution of a named published conjecture is claimed.
- No universal classification of all surcomplex elliptic curves is claimed.
- No classical covering-space or contour theory on the fine topology is used.
- No convergence of degree truncations in the full higher-rank valuation
  topology is assumed.
- No algorithm deciding arbitrary surreal exponent comparisons is supplied.
- No full-domain homomorphism with the same period kernel is asserted.
- No compiled Lean theorem or repository build is claimed for this new work.

## Artifact validation

The source compiled with pdfLaTeX without warnings after three passes. The
21-page PDF was rendered and visually inspected, with no detected clipping,
missing references, or mathematical glyph errors. These are document-quality
checks, not mathematical proof certificates.

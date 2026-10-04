# Mathematical proof audit

This is an internal review record, not an independent referee report or a
proof-assistant certificate. Theorem numbers refer to the delivered article.

## Core dependency graph

1. Proposition 2.2: left-finite supports are preserved by addition,
   convolution, and geometric inversion. Every bounded output prefix uses
   finitely many terms. This establishes a field without appealing to
   closure of an arbitrary subfield of a Hahn field.
2. Proposition 2.3: simultaneous stabilization of finite valuation prefixes
   proves metric completeness. Finite-support series are dense. The
   coefficient field is discrete for this topology.
3. Proposition 3.1: simple-root Newton iteration proves henselianity.
   The residue-characteristic-zero defectless theorem, together with a
   divisible value group and algebraically closed complex residue field,
   proves algebraic closedness after adjoining i, hence real closedness.
4. Theorem 4.1: real closedness makes order intrinsic. Rational isolating
   intervals force every embedding to fix real algebraic constants.
   Archimedean comparison is preserved in both directions, inducing an
   ordered value-group injection. Equality of rational cuts shows that
   this injection is positive scalar multiplication.
5. Theorem 4.2: monomial characters define embeddings on the dense group
   algebra and extend to its completion. Valuation scaling prevents
   leading-term cancellation. Forward summability is proved separately
   and does not imply surjectivity.
6. Lemma 5.1 and Theorem 5.2: finite rational rank makes the value map onto
   and supplies finitely many positive unit-correction bounds. Their
   minimum is a uniform valuation gain. Both Neumann inverse identities
   follow by finite telescoping and passage to the limit.
7. Lemma 6.1 and Theorem 6.2: an independent exponent chain approaches a
   finite limit. The shift character defines an isometric embedding.
   The telescoping boundary term forces infinitely many nonzero
   coefficients below a fixed bound in any putative preimage. Such a
   preimage is forbidden by left finiteness.
8. Theorem 7.1: the same coefficient argument excludes even approximation
   with error valuation at least the limiting exponent. Finite telescopes
   approach this exact supremum without attaining it.
9. Theorem 8.1: independent chains encode subsets of N in omitted
   monomials. Finite-support approximation plus isometry proves joint
   continuity of the embeddings. Countably many dense test points prove
   lower-Vietoris continuity and Effros Borel measurability of the ranges.
10. Theorem 11.3: an integer part of the whole field, contained in a
    cofinal-valued subfield, supplies arbitrarily precise approximations
    after scaling. Thus a closed such subfield must be the whole field.

## Essential hypotheses checked

- Coefficients are the real algebraic numbers. This is needed for automatic
  coefficient fixing in the abstract-field statement. A coefficient-fixing
  variant is a different claim.
- Gamma is a nonzero divisible Archimedean ordered group, given as a
  Q-vector subspace of R. Rational rank is not ordered-group rank.
- Countability is required for Polishness and the stated Effros-space
  formulation, not for the algebraic finite/infinite rank dichotomy.
- Supports are left finite, not merely well ordered. A bounded increasing
  infinite support belongs to a full Hahn field but not this field.
- A positive uniform valuation increment tends to infinity under iteration
  because the valuation is real valued. Merely strict pointwise gain is
  not enough.
- Newton's simple-root argument starts with a in the valuation ring and
  a unit derivative. The defectless input uses residue characteristic zero.
- 'Immediate' refers to unchanged value group and residue field. It does
  not mean dense or surjective.
- A complete isometric image is closed. Completeness only supplies limits
  of Cauchy sequences; the formal inverse in the counterexample is not
  Cauchy.
- The range parametrization is not asserted to be continuous for the full
  Vietoris topology, and inclusion of parameter sets is not asserted to
  imply inclusion of image fields.
- The canonical integer part and a transported integer part need not be
  the same ring. A transported integer part of the image need not be an
  integer part of the ambient field.
- Surreal realizations are set-sized and use the transported valuation
  topology. Neither a topology nor an embedding of the entire proper
  class of surreal numbers is constructed.

## Literature correction

The inspected text is arXiv:2107.03362v3, Definition 4.2.3 and Lemma 4.2.4,
printed page 24. Definition 4.0.3 on page 20 fixes the summability notion.

The counterexample on k(t) sends t to t+t^2. Every rational Laurent
expansion is forward summable with rational-function output. The reflection
t -> -1-t fixes the image field k(t+t^2) and moves t, proving properness.
The source's convention allows k(G) itself as a Hahn field; k(t) therefore
lies in its stated domain. The complete infinite-rank left-finite example
shows that completeness and real closedness alone do not repair the
one-sided implication.

No claim is made about a correction in the final journal version, an
exhaustive search for errata, the validity of every other result in the
paper, or external confirmation by its authors.

## What the finite checks establish

The script checks exact rational binomial identities, principal-root
identities, Neumann identities in Q[t]/(t^25), the Catalan inverse through
degree 24, finite shift telescopes with their boundary term intact, and
the rational-function reflection identities. Formal chain symbols are not
numerical approximations to independent real exponents.

They do not establish any infinite support, completion, real-closedness,
model-theoretic, basis-existence, or novelty claim. No proof assistant was
run for this new manuscript.

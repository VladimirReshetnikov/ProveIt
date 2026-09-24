# Proof audit

This is an author-side mathematical audit, not independent review or machine
verification. The PDF contains the complete arguments and explicit imports.

## Principal dependency chain

1. Surreal normal forms give a constant-term map Oz → Z, support projection,
   an omnific floor, and monomial bounds for set-sized supports.
2. The determinant trick gives monic radical-ideal certificates.
3. The dominant-scale quadratic splitter preserves every nonzero earlier
   Boolean atom against all possible global radical-ideal witnesses.
4. A countable closure construction produces B = E ∩ Oz, not merely a subring
   of Oz. E is real closed, Frac B = E, |E| = κ, and J² = J.
5. The global certificate obstruction transfers to the set-sized normalization
   of A = B_J: every finite splitter atom survives its reduced closed fiber.
6. For each finite pointed quadratic neighborhood, every possible denominator
   outside the residue prime evaluates nontrivially on every generic branch.
   This is Lemma 5.2, the main bridge to henselization.
7. Faithful flatness embeds all these finite products into the generic fiber.
   The resulting idempotents contain a free Boolean algebra on κ generators.
8. The equation u² − u + ω = 0 forces a square root of −1 *in the generic
   fiber*. It does not produce one in H, which still has residue field Q.
9. An ind-étale algebra over a real closed field containing E[i] is a directed
   union of finite E[i]-products. Its spectrum is a Stone space and it is a
   locally constant function algebra. Compactness and the free Boolean family
   give the exact cardinal 2^κ.
10. Flat going down identifies these generic points with the minimal primes
    of H. The idempotent maximal ideal separately makes all adic quotients Q.

## Checks against common errors

- Projection onto a subgroup is linear over the retained Hahn field, not a
  ring homomorphism on the full surreal field.
- Specialization T → 0 is defined on a finite quadratic algebra. It is never
  applied to the Laurent field or to an infinite Laurent expansion.
- The main localization lemma treats every denominator, not only the visible
  coefficients in the defining equations.
- All prime-ideal and compactness arguments take place in set-sized rings and
  spaces. Global normalization notation abbreviates finite certificates and
  congruences, not a set of proper-class cosets.
- The polynomial splitter comes from the repository. Its reproof is included
  to make the new henselian bridge independently readable.
- H and H[i] are local. Nontrivial idempotents occur only after generic base
  change. Neither local ring is identified with a product of branches.
- The Gaussian product is an E-algebra/ring decomposition; its two factors
  have conjugate scalar actions for the external E[i].
- Strict henselization uses the actual coefficient section Q → H and a chosen
  algebraic closure of its residue field. Its Galois-product description
  depends on an embedding Qbar → E[i].
- No Noetherian assumption is smuggled into the cardinal or henselian proof.
  The constructed rings are explicitly non-Noetherian.
- There is no assumption κ is regular, and no use of CH, GCH, or a large
  cardinal axiom. Birthday-bounded realizations are not asserted.

## External mathematical imports

The main proof imports standard surreal normal-form/real-closedness facts and
ordinary commutative algebra, including henselization, faithful flatness,
reducedness under henselization, and étale algebras over fields. Their sources
are identified in the article. The centered valuation-space corollary further
imports de Felipe–Teissier, Corollary 4.2; that external theorem is not reproved.

## Computational scope

The 5,760 exact assertions include 5,586 finite Boolean atom assertions.
The count is not a measure of proof strength. The other groups check the
quadratic identity, its two specializations, the first Laurent coefficients,
the generic coordinate change, forced complexification, finite support
projection, Gaussian product maps, and a finite Galois splitting matrix.

These computations do not prove infinite-support claims, exclusion of all
possible denominators, prime existence, cardinal arithmetic, or historical
novelty. No Lean development is included and no repository build is claimed.

## Remaining uncertainty

Independent checking of the entire proof, especially the support-to-localization
bridge, is warranted. Historical priority is provisional. The exact Stone space,
atomlessness, arbitrary hull enlargement behavior, mixed-characteristic
analogues, and full class-level geometry are not settled by this article.

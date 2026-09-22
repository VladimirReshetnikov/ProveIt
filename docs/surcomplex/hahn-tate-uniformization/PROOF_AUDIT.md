# Proof and novelty audit

## Candidate-original package

The central result is the conjunction of an exact maximal literal Hahn-series domain with surjective elliptic uniformization on that domain, at arbitrary valuation rank. The article proves the additional support and lifting steps; it uses the established complete rank-one Tate theorem as an explicitly identified classical input.

“Not identified in a targeted search” is the novelty status. It is not a guarantee of absence from the literature, a peer-review certificate, or a claimed solution of a previously named open problem.

## Proof dependency map

1. **Classical Hahn–Neumann/Higman calculus.** Positive supports generate well-ordered monoids with finite decompositions. The article recalls a proof using Higman's lemma and cites the classical sources.
2. **Exact domain.** The theta leading exponents are n(n−1)alpha/2 + n beta. The two Tate coordinate families have their own explicit leading-exponent obstructions. The support proofs are separate.
3. **Coarse formal evaluation.** Coefficient series in K_H may have arbitrarily negative fine valuations. Positive quotient values of the substituted variables give finite contributions in each quotient fiber. This is proved in Lemma 5.1.
4. **Rank-one reduction.** K_H is complete for the rank-one coarsening obtained by quotienting out values infinitesimal relative to alpha. A direct Cauchy-sequence proof is provided.
5. **Classical Tate theorem.** Surjectivity and the group law over complete real-valued non-Archimedean fields are imported from Tate, not reproved or claimed as new.
6. **Taylor/Hahn agreement.** Lemma 6.3 proves the joint-family interchange: quotient Neumann finiteness controls Taylor degree, and cofinality inside H controls the rational tail index. This is a particularly important independent-review target.
7. **All-rank group law.** Classical local identities are evaluated through the coarse formal homomorphism in regular projective charts. The argument does not apply a singular affine chord formula at a zero denominator.
8. **Surjectivity and kernel.** Good coarse reduction plus the invertible formal parameter z = -x/y gives every infinitesimal lift and makes the kernel exactly q^Z.
9. **Torsion arithmetic.** A binomial root removes the unit part of q. Finite exponent-coset decomposition gives the extension degree. A character-Galois stabilizer calculation proves that one specified torsion point generates it.
10. **Surcomplex transport.** Every instance lies in a set-sized normal-form workspace; strong functoriality makes the result independent of its enlargement.

## Classical material not claimed as new

Tate's original rank-one uniformization; the theta triple product; the Tate discriminant and modular invariant; the inverse j-series as a formal series; standard elliptic n-torsion and classification by j; algebraic closedness of a divisible Hahn field over C; and the Kummer description of Tate torsion.

The torsion contribution is an exact arbitrary-exponent-group formulation within the support-controlled all-rank theory, not a new discovery that Tate torsion comes from roots of q.

## Essential qualifications

- Maximality concerns the *specified bilateral families and strong Hahn summability*, not every imaginable extension or resummation.
- Nondivisible exponent groups are permitted for E_q, but arbitrary curves with the same j can be twists over such a field.
- The negative-j regime is covered. A uniformization of every elliptic curve in the good-reduction regime is not asserted.
- The value-circle exact sequence is algebraic and circularly ordered. No unrestricted real-metric Berkovich skeleton theorem is claimed at higher rank.
- Differentiation is with respect to an external variable. It is not the Berarducci–Mantova derivation on surreal scalars.
- Strong sums need not be limits of their partial sums in the full valuation topology.
- The computations are finite consistency checks, not machine-checked proofs of the paper.

## Recorded verification

All included checks passed. See `data/verification.json` for the exact scope, coefficients, and runtime versions. No floating-point numerical test is used, and no Lean compilation or independent human peer review is claimed.

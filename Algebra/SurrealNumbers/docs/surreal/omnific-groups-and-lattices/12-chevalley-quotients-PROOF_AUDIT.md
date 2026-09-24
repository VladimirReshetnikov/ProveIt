# Proof audit and dependency checks

This is the manuscript's own proof-audit record, not an independent referee report or a formal proof certificate.

## 1. Scalar collision

For a fixed nonzero a in Pi_k and a set-sized target S, take a set field F0 with more elements than S. Its supports form a set, so there is a positive surreal M larger than every absolute support exponent. A positive delta can be chosen with 3 delta M below every exponent of a. Exponent compression is an order-preserving automorphism of the additive exponent group and therefore induces the stated normal-form field automorphism.

For F = T_delta(F0), u = omega^(delta M), and v = a/u^2, all of uF and v lie in Pi_k. A collision between uf and ug gives a killed parameter u(f-g). Since 1/(f-g) belongs to F, multiplication by u/(f-g) kills u^2 and then a. Neither a lower bound in R nor a minimum support exponent is assumed.

## 2. Root reconstruction

The common kernel of the finitely many root maps is additive. For r in that common kernel and arbitrary s in the ideal, the proof kills the root images of rs.

- A2 gives the product directly.
- B2 long roots use a half of the unrestricted second parameter. Short roots are then handled by removing a long-root error already known to vanish.
- G2 long roots use their closed A2 subsystem. The short–short formula has a coefficient-2 short term and two long terms with coefficients 3. Halving the unrestricted second parameter obtains rs, and the long terms are multiples of r by elements of the ideal.

There is no inference r/2 is in the common kernel, no division in the target group, and no division by 3 in the G2 argument. Root-system transport does not assume invariance of the target kernel under the Weyl group.

The image carrier is an actual subset of H^Phi. Multiplication is transported from I after proving the ideal condition; it is not target group multiplication. No set of class-sized cosets is used.

## 3. Intrinsic kernel maps

The constant-term kernel is a normal closure by a finite-word replacement argument using the split retraction. A homomorphism defined only on that kernel is applied to each conjugate of the root-generated subgroup separately. It is not assumed to extend to the ambient elementary group, and the un-conjugated root-generated subgroup is not assumed normal.

The Steinberg proof uses only its root presentation and the same normal-generation argument. Its constant-term kernel is not identified with K2.

## 4. Structure and central forms

Each ideal element is a single product of two ideal elements. Rootwise commutator formulas give perfectness and a bound of at most three commutators per root element, not per arbitrary kernel element.

Finite-order matrices over A have ordinary roots of unity as eigenvalues. Their characteristic polynomials equal their constant terms and hence (X-1)^N, forcing identity. Centrality in the elementary kernel yields polynomial commutation with every root parameter; the standard finite center of the ambient semisimple group supplies the remaining argument.

A central isogeny's elementary kernel consists of ordinary points, hence constant elementary points after applying the retraction. It meets the relative kernel trivially. Lifting a relative point and removing its constant term proves the claimed isomorphism of relative kernels.

Nonsimplicity uses the ideal (1+omega). The quotient omega/(1+omega) is finite but nonconstant, so it is not in A. This proves the required properness of the congruence subgroup without asserting every ideal is classified.

## 5. Rank-one boundary

The highest-degree term of a reduced amalgam word uses every positive-degree parameter. Its coefficient is the product of the nonzero interior lower-left constants times g0 E12 gm. Every other term has strictly smaller degree, so the highest term cannot cancel.

A finite set of nonzero syllables can be simultaneously detected by a coefficient functional into Q or Q(i). It is equivariant for the constant upper-triangular action. This gives a countable amalgam target and retains reducedness. The map is additive, not multiplicative. Proper-class residual detection rules out a universal set-sized quotient.

## 6. Lie classification

Rational perfection implies that one integer m clears all bracket expressions for an integral basis. In the ideal argument, m is divided only in the unrestricted source parameter. Thus arbitrary set-sized Lie rings, including torsion targets, are covered.

Nonperfection gives a primitive integral covector annihilating brackets and a surjection onto the abelian additive ring A. Coefficient functionals detect every nonzero additive element in a set-sized target. The argument uses the fact that universal quotients descend along surjections, not merely the existence of one character.

## 7. Cardinal estimates

The ring carriers lie in finite powers H^Phi or M^d. For an infinite threshold kappa, a finite power of a cardinal less than kappa still has cardinality less than kappa. The transfer itself needs no regularity assumption; the existence of collision data in a particular Hahn fragment may need one.

An action on X has target Sym(X), of cardinality 2^|X| when X is infinite. No incorrect replacement of this cardinality by |X| is used.

## 8. Computational boundary

The accompanying run passed 2,188 exact checks: polynomial matrix identities, integral divided powers, finite root configurations, and finite rank-one word calculations. These checks do not prove the class-theoretic support argument, arbitrary homomorphism statements, or all unbounded classical ranks. Those are written-proof claims requiring independent mathematical review.

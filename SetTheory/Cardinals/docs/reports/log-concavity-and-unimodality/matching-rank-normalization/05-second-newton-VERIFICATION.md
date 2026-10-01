# Exact verification scope

The main finite proof input is the nonnegative coefficient expansion of every
cleared core Schur determinant on every chosen exterior-basis cone:

- 61 rooted core orbits: 24, 24 and 13 by forced core-column size
- 51 Hall-matchable exterior-left basis multisets for every core
- 3,111 determinant polynomials
- 50,037,694 nonzero coefficient entries, all positive integers
- Minimum positive coefficient 1; absent monomials have coefficient zero
- Polynomial degrees 10, 12 or 14

The primary generator uses an exact inclusion-exclusion expression for the
three-column endpoint count, symbolic rational Schur elimination, and repeated
unit population shifts. The independent implementation uses Hall's criterion
on labeled row supports, verifies the supplied inverses by multiplication, and
translates each population by its full multiplicity in descending coordinate
order. All per-basis hashes, counts and minima agree exactly.

The independent reconstruction separately checks all 61 orbit representatives,
all 51 basis profiles, 1,032 endpoint-polynomial identities, 61 direct Hall
reconstructions of the total-B coefficient, 14 R-feature relations and 48
finite-graph quadratic-form identities with arbitrary signed test vectors.
Further direct endpoint-state checks pass 98,816 identities on 1,536 rooted
labeled graphs. All 64 empty-core-column Schur identities and the fifth-degree
Lorentzian obstruction pass exact checks.

The supporting finite graph examples do not replace the universal proof. The
infinite-population conclusion follows from the complete nonnegative polynomial
identities on all basis cones, the exact class-limit quadratic identity and the
positive Schur denominators.

The mathematical reduction and full manuscript passed independent review.
The finalizer checks the immutable generator, runner and inverse checksums,
the complete orbit and basis lists, and every recorded normalization. The R-determinant
checker uses explicit RuntimeError checks so optimized Python cannot bypass it.

Use the default verify.py command for a fresh full reconstruction. The optional
quick mode is only an integrity and sample replay. The package includes the
recorded full results so these two modes cannot be confused.

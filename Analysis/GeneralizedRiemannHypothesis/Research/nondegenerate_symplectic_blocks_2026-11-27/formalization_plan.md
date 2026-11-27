# Formalization plan and precise status

This is a specification and dependency plan, not compiled Lean code.
The new theorem was proved on paper and checked with exact arithmetic and
independent enumeration. The upstream GRH development was inspected but not
rebuilt or replayed in this session. Its machine checks do not formally verify
the new theorem in this archive.

## Mathematical objects

Fix a finite field K of cardinality q and an even natural n=2m. Define a
nondegenerate alternating form J on K^n, its perpendicular sum with itself,
the finite symplectic group preserving that sum, and the upper block map.
Define the two probability mass functions by finite counting: pushforward of
uniform counting on the group, and uniform counting on all square matrices.
Define D(M)=J-M^T J M and nullity as the dimension of its kernel.

## Suggested module order

1. **AlternatingFrames**: symplectic basis extension; order of the finite
   symplectic group; injective prescribed-Gram frame count E(D,j,s).
2. **DegenerateAlternatingSpaces**: the radical splitting and the automorphism
   count `Sp_(2s) * GL_t * q^(2st)`; type count C(D,j,s).
3. **CompressionLikelihood**: uniform first-column frames; count the lower
   block by its radical kernel; derive the likelihood alpha*F(k).
4. **OptimalDetector**: prove F(0), F(1), the maximal-isotropic lower bound,
   likelihood sign separation, and both exact total-variation identities.
5. **KernelMoments**: finite expectation identities for block nullity and
   defect nullity; map-count conversion to q-power moments.
6. **GeometricInterpolation**: exact indicator polynomials on q^a and q^(2a),
   the coefficient bounds, and summability of the resulting Gaussian series.
7. **SharpAsymptotics**: uniform second-order product estimates, signed
   candidate measures, interpolation-tail bounds, and the two L1 expansions.
8. **StatisticalSeparation**: the positive full-matrix limit, sharp rank TV,
   and equal-prior optimal testing interpretation.

The finite identities should be formalized before real asymptotics. This
keeps delicate infinite-product, summability, and big-O dependencies out of
the algebraic counting layer. Characteristic two must retain the condition
`B(v,v)=0`; skew symmetry alone is insufficient there.

## Existing proof connection

The conceptual starting point is the source's finite compression theorem
`New/Spanning/SecondMoment/PositiveType.lean` and ProveIt's matrix-statistics
section. The new finite-group theorem can be formalized independently of the
GRH project. Importing the final GRH theorem is neither needed nor useful for
this proof.

## Verification gates before any formal claim

- Check actual statements against the intended nondegenerate block model.
- Compile the entire transitive dependency closure.
- Print axioms for the final declarations.
- Check that no admitted theorem is imported by those declarations.
- Preserve a pinned toolchain, dependency manifest, build log, and source hash.

None of those gates is asserted completed for the new theorem here.

# Mathematical review checklist

This is the preparation review record, not an independent referee report.

## Checked distinctions

1. **Real vs surreal coefficients.** The simultaneous compression theorem
   concerns real linear combinations. It does not assert preservation under
   arbitrary surreal coefficients or nonlinear polynomial operations.
2. **Set vs class.** Each normal form has set-sized support. Finite
   statements are interpreted inside an adequate set-sized ordered field;
   real closure is used only where needed.
3. **Affine gauge.** The q-scale bound is for the nonaffine height component.
   The removed affine component can retain arbitrary support.
4. **Exact zeros.** The stopping condition says every coefficient row lies
   in the selected span. This proves kernel equality, not just agreement
   on a finite sample of nonzero signs.
5. **All leading levels are attained.** For each pivot, separate it from
   the previous row span by a real linear functional.
6. **Degree lower bounds.** Equality of complete sign types forces equal
   kernels. A degree-D polynomial contributes at most D+1 coefficient
   functionals, or D+r_0 when the constant term is fixed.
7. **Quantifier order.** For complete dependence types, each fixed real test
   stabilizes near zero; no common positive real parameter works for all
   tests when m >= 2. Finite test lists admit a uniform parameter.
8. **Linear path.** Standard part preserves weak signs. Combining a weakly
   correct shadow with a strictly correct endpoint preserves every strict
   sign throughout the punctured segment.
9. **Toric ideals.** Graver decomposition is conformal; the tie case is
   handled separately. Arbitrary ideal polynomials are reduced to their
   toric-homogeneous parts before comparing weights.
10. **Shadows.** Standard part commutes with finite convex hulls, but a
    face's shadow need not be a face. Scalar extension changes the set of
    convex combinations even when vertex labels are unchanged.
11. **Validity radius.** Only the validity component adjacent to zero is
    the initial interval. The global set may be disconnected.
12. **Computability.** A known complete finite coefficient list is not the
    same representation as a coefficient oracle with a finite-support
    promise; the latter can encode halting.

## Deliberately unclaimed

- No new finite real-unrealizable polytope face lattice.
- No isomorphism of the entire surreal scale field with one-parameter
  Laurent/Puiseux series preserving all multiplicative comparisons.
- No polynomial arc theorem for arbitrary nonlinear constraints.
- No new comprehensive higher-rank tropical duality or multiplicity theory.
- No new Lean verification, exhaustive priority audit, or independent
  peer review.

## Executed checks

`python3 code/verify.py` passed all 53 exact finite cases. The output files
record the reproducible certificate data. The verifier checks determinants,
slacks, leading terms, zero status, rational specialization, and sample
points of the proved linear paths. The general toric, class-field,
curve-selection, and undecidability arguments are mathematical proofs,
not implemented algorithms in this package.

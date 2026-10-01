# Mathematical self-audit

This is an internal proof review, not independent refereeing or formal verification.

## Main boundaries checked

1. **Normalization.** Mixed volume is normalized by V(P[d]) = Vol_d(P). For d segments it equals |det|/d!. The zonotope expansion has factor 2^d/d!. The planar hidden-shear identity is delta + |h|/2, not delta + |h|.

2. **No cancellation shortcut inside determinants.** Determinants are evaluated exactly. Cancellation-free valuation applies only to their finite sum of absolute values after the zonotope comparison.

3. **Ordinary comparison constants.** For m+1 displayed generators, P-c is contained in its displacement zonotope, which is contained in m(m+1)(P-c). These are ordinary integers, so they have valuation zero. No rank-one or completeness assumption enters this step.

4. **Degenerate arguments.** The colorful formula allows lower-dimensional polytopes and point arguments; an empty or all-zero minimum is infinity. Spectrum classification and adaptive recognition assume full rank. Partial perturbation results are phrased in terms of the surviving minors if rank drops.

5. **Finite generation.** Principal determinant ideals, minimum pivots, and a basis selected from the displayed generators all use finite generation. No conclusion is automatically extended to arbitrary convex sets or infinitely generated modules.

6. **Adaptive versus nonadaptive quantifiers.** The d+1 test recognizes the module of a known reference. It does not reconstruct an arbitrary unknown module using a fixed universal set of probes. The planar obstruction quantifies over every fixed finite test family and then constructs two indistinguishable modules.

7. **Non-Archimedean hypothesis.** The negative theorem explicitly assumes a positive infinitesimal. Its pair has exactly the same area, spectrum, standard part, and entire residue flag. The module distinction is witnessed by the nonintegral relative shear h/delta.

8. **Rank-two sufficiency.** The interval theorem includes realization of every value, using a unit lower-triangular matrix with prescribed shear valuation. It does not derive sufficiency merely from Alexandrov–Fenchel.

9. **Higher-dimensional limitation.** Complementary minors of one integral invertible matrix are jointly constrained. The manuscript does not treat their valuations as independent parameters and does not claim the higher-dimensional realization problem solved.

10. **Polarity.** The exact duality is stated for origin-symmetric, full-dimensional polytopes. The volume-product assertion is only a valuation-zero statement, not a real coefficient bound or a solution of Mahler's conjecture.

11. **Field size.** The main arguments take place in a set-sized real-closed field containing the finite surreal data and R. Scalar extension preserves the finite determinant comparisons. No class-sized measure is invoked.

12. **Computation.** The supplied checks use Q(t) and test finite instances. They do not validate arbitrary surreal representations, prove universal formulas, or constitute Lean kernel verification.

## Certificate implementation boundary

The module and matrix statements can be checked from exact generator identities, integrality inequalities, and unit determinant certificates. To obtain a formal theorem about mixed-volume valuations, a proved finite-polytope mixed-volume interface and the colorful bridge are still required. No untested Lean code or admitted stand-in is included.

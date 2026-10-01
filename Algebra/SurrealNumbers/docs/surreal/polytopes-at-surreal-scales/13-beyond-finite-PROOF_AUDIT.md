# Internal proof review

This is an authoring-stage review, not an independent referee report or a
proof-assistant certificate. The theorem numbers refer to article.tex.

## Logical prerequisites

NBG with Global Choice, in one fixed universe; full current-universe No;
ordinary finite dimension; classical real closedness and the realization
of every set-sized cut, with empty sides allowed. Finite polyhedral facts
are used over ordered fields. Quantifier elimination, compactness, and
ordered real-closure uniqueness are classical inputs.

## Reviewed arguments

1. **Small-type realization (2.2).** Put parameters in a set-sized real closed
   subfield. Transfer finite existential consistency by quantifier elimination.
   Use compactness for a set-sized extension, then embed it into No fixing
   that subfield by set-length cut recursion. No ordinary set model whose
   domain is all of No is assumed.
2. **Facial traces (3.2–3.4).** Every positive generator in a face-valued convex
   combination belongs to the face. Gather all witnesses into one finite
   hull for the converse facial criterion. Feasibility of the finite affine
   sign conditions is invariant under ordered-field extension.
3. **Uniform separation (4.1).** Both sides are nonempty. Finite subsystems
   can be supplemented with a fixed point from each side, strictly separated,
   and rescaled. The global margin is a positive surreal margin, not necessarily
   a positive real margin after normalizing the normal vector.
4. **Exposure (4.3).** A nonempty proper face has both an inside and an outside
   generator. Finite-polytope faces have positive finite-list slack. The unit
   slack is imposed on outside generators only, not on all points outside
   the face. The latter false assertion is explicitly excluded.
5. **Active faces (5.2).** A single positive radius lies below every inactive
   normalized slack. Local feasible directions are the kernel of the active
   normals. A basis of at most d active rows has the same kernel. Relative
   interior and the segment definition identify the minimal face. A proper
   active slice has a nonzero sum normal.
6. **Finite sandwich and rigidity (6.1–6.2).** The type of all input membership
   conditions plus nonmembership in every finite subhull is a set. Combine
   finitely many forbidden hulls by taking the union of their generators.
   Saturation rules out failure of every finite sandwich. Equality gives
   the inclusion cycle and simultaneous compression of the original lists.
7. **Polarity (7.1).** The hypotheses include full dimension and the origin
   in the interior. These give boundedness of the polar and its interior.
   Strong separation with 0 in the primal makes the normalizing scalar
   positive. Finite compression then proves the small-generation equivalence.
8. **Infinitesimal degree (8.2).** Coefficients are real. The first nonzero
   real coefficient determines the sign at a positive infinitesimal. A
   polynomial cannot vanish there unless all coefficients vanish. Deleting
   constant stages gives the converse degree bound. The invariant and its
   classical dimension bound are credited to Martínez-Legaz.
9. **Sharp family (9.1–9.2).** Testing both signs of arbitrarily small real
   tangent vectors on the paraboloid forces a supporting normal at 0 to
   be purely vertical. The exposed base is therefore forced at every step.
   Product restriction proves sharpness for all face codimensions.
10. **Moment hull (10.1).** Square products provide every listed face.
    Conversely normalize all coefficients of a nonzero surreal exposing
    polynomial by their maximum absolute value. At least one normalized
    coefficient is exactly +/-1; the real standard-part polynomial is
    therefore nonzero. Positivity on Q makes it nonnegative on R, and distinct
    real roots consume even multiplicity. Thus there are at most floor(d/2)
    active rational parameters.
11. **Moment polar (10.2).** Active parameters are a primal exposed face, so
    there are at most floor(d/2). Taking a scalar product with the feasible
    normal turns a linear relation among active rows into an affine relation
    among moment points. Vandermonde independence gives full row rank.
    The explicit normal u_A/alpha_A has exactly A active, with alpha_A the
    positive average of q_A(0),...,q_A(d). This proves existence, dimension,
    and the complete reverse-inclusion face correspondence.
12. **Cardinal version (12.1–12.2).** All types, finite-subset families, and
    parameter fields stay below the stated uncountable kappa. For the cut
    converse, choose the realizing extension below kappa by downward
    Löwenheim–Skolem before beginning the embedding recursion.

## Important excluded inferences

- Small generator sets do not mean small convex hulls.
- Closed and bounded does not imply compact or imply extrema exist.
- Exposure does not imply that there are any proper faces or any vertices.
- A set of valid inequalities need not be a complete H-presentation.
- Finite certificates for each consequence do not imply a finite presentation
  of the full H-class.
- A real body's generator extension is not its semialgebraic No-extension.
  The article gives the exact positive value epsilon^2/4 witnessing the difference.
- Countably many rational samples do not prove an assertion about every rational
  parameter, still less every surreal parameter.
- No new finite-polytope combinatorial type or named classical conjecture is claimed.

## Remaining independent review targets

The proofs should be independently reviewed, particularly the class/set
formalization and the exact relationship between generator extension and
face traces. Priority of the infinitary convexity consequences should be
checked against the literature on saturated fields, externally definable
convexity, and non-Archimedean separation. None of these review tasks is
represented as already completed by the finite regression program.

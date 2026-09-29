# Proof and scope audit

## Mathematical target

Theorem 3.1 gives the height of K(sum_Q P_q), where Q is finite nonempty, every
P_q is a WPO, and every h(K(P_q)) is an infinite pure power omega^(rho_q), rho_q>0.
Theorem 7.2 compresses the calculation to maximal antichains. Theorem 9.2 extends
ordinal-chain inputs to all nonzero limit ordinals by finite block expansion.

## Classical inputs

1. Finite Hoare powersets of WPOs are WPOs (obtainable from Higman's lemma).
2. Wolk's theorem: a WPO has a chain attaining its rank-defined height.
   A compactness proof via finite rank levels is included in Section 2.1. It uses
   the standard compactness of a product of finite discrete spaces in ZFC.

The chain theorem is not assumed for arbitrary well-founded posets. No result
about maximal linear-extension type is used. No unrefereed ProveIt theorem is
a premise of the new proof. The earlier uniform formula is recovered as a
corollary of the independently given argument.

## Main proof checks

- A finite cofinal subset of a fiber would make K(P_q) have a greatest element,
  giving successor height. A positive pure-power height therefore forbids this.
- The support of a nonempty compact downset is a finite ideal. Its maximal
  support vertices have nonempty compact coordinates; other support fibers
  are wholly included. Profile inclusion retains the inequalities on common
  active coordinates.
- A chain has only finitely many distinct supports. In an earlier support
  segment, an actual later profile bounds every persistent coordinate.
- Add one to each such coordinate rank to get a strict ordinal bound. The
  limit hypothesis ensures this still lies below the component height.
- Every persistent coordinate is charged at a later retirement or terminal
  stage. Its earlier bounded natural-sum contribution is below a future pure
  maximum, and is erased by ordinary ordinal addition of that future suffix.
- The lower construction varies only a coordinate which is about to retire;
  every coordinate persistent across blocks stays at its fixed base until its
  own later block. Component chains need not be cofinal.
- Refining a support path cannot decrease its value. Ordinary ordinal addition
  is monotone in both arguments, even though it is not strictly monotone in the
  left argument. This is enough for the dynamic-programming optimal-substructure
  argument.
- Canonical maximal antichains are Min(Q minus the completed part). At a
  one-vertex support extension, their difference equals the actual retirement
  set exactly. This proves compression rather than assuming strata are
  universally comparable.

## Additional consequences

- A common pure value h(K(P_q)) is sufficient for component replacement in
  finite lexicographic substitution. h(P_q) alone is not asserted to suffice.
- Positive limit ordinal fibers admit finite CNF expansions into pure blocks.
  Exponents are not recursively expanded; arbitrary exponent labels are allowed.
- The finite exponent order/equality pattern determines all coefficient vectors
  and all optimal schedules. An algorithm comparing arbitrary ordinal-notation
  strings is NOT supplied.
- Distinct retirement groups partition Q. Choosing one maximum per group proves
  the n-term coefficient budget and the natural-sum upper bound.
- The isolated-high-coordinate plus finite-chain family proves that even a fixed
  maximal-antichain poset with identical local stratum heights can have m distinct
  global heights alpha, ..., alpha*m.

## Explicit boundaries

- Empty Q: h(K(empty))=1, handled separately.
- Finite or successor components are not admitted to the pure-height theorem.
- General nonpure WPO components are not covered by the ordinal CNF expansion.
- Infinite skeletons require new limit-stage arguments.
- The theorem computes height, not width or maximal linear-extension type.
- It does not justify arbitrary repeated application of K without new input
  component-height calculations.
- Set-sized instances in ZFC are used; no proper-class rank object is claimed.

## Computational status

The code has been executed. See data/verification.json for exact counts.
Uniform maximal-antichain heights are also computed using finite integer ranks.
Weighted support and compressed DPs agree with exhaustive extension enumeration
on the stated instances. Sampled profiles check comparison, not infinite ranks.
Certificates are checked without calling the optimizer. Tampering tests cover
wrong answers, state values, frontiers, predecessors, and missing states.

No Lean installation or Lean build is claimed. The transfinite arguments are
written proofs, not mechanically verified proofs. They have not been independently
refereed. Priority is not certified by the limited literature search.

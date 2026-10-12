# Mathematical review checklist

The following are explicit proof obligations checked against the manuscript
and implementation, not claims of machine-verified proofs.

1. A positive zero-parent-port assignment can be extended by zero only because
   all model constraints are homogeneous and forbidden pairs are local.
2. A normalized unbounded compatible optimization problem has a positive
   zero-port recession direction in one fixed coordinate face/sign chamber.
3. Unavailable signs are not confused with zero slopes; the negative verifier
   checks availability independently from the objective value.
4. Coordinate restrictions define faces of local nonnegative sign chambers,
   so filtering complete original local ray lists remains complete.
5. Source fluxes are signed. Cut rank zero requires explicit zero-flux equations.
6. Cut-space membership and dimensions are checked against the original source,
   and every original forbidden pair remains in exactly its source bag.
7. Zero SOURCE flux splits a vector into disjoint feasible coordinate pieces.
   This property fails for arbitrary redundant scalar presentations.
8. The no-new-rays argument uses the occupied tree component after removing
   zero-flux edges and a small perturbation in its original coordinate face.
9. Gluing selects individual local extreme rays, never an average of tied
   optimizers, and uses zero on zero-port child subtrees.
10. Primitive standard-normal rays are connected by component additivity and
    integer divisibility along a primitive ray. No essential-disc conclusion
    follows from connectedness and positive Euler value alone.
11. The implemented bound uses RAW nullity; the stronger intrinsic-dimension
    bound assumes an exact polynomial-time LP primitive not delivered here.
12. Message bits are bounded using original normalized subtree systems or
    products of local ratios along simple paths, not by unit-cost arithmetic.
13. The gain chain is algebraic and analytically soluble. Its literal enumeration
    comparator is not asserted to be optimal.
14. The rank-two obstruction concerns literal convex-cone lists only.
15. Complete recognition additionally charges all source, geometry, and
    decomposition-producer costs; supplied decomposition verification is not
    decomposition discovery.

Executable complements: generic redundant-port counterexample; 455 compiled
source-extremality checks; source-rank rejection and generator mutations;
1536 independent result replays; actual fixture rank-three rejection and
rank-one nongeometric split; malformed and incomplete result packet tests.

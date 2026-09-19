# Review notes

## Exact claim

The formula U in Theorem 1.1 equals the least operation satisfying the two
axioms stated in equations (3) and (4). The claim is for countable sequences
with arbitrary ordinal entries. It is not restricted to eventually constant
sequences or entries below epsilon_0.

The public problem used is Problem 6.2 of arXiv:2505.00424v2, dated
30 April 2026. No exhaustive priority claim is made.

## Proof dependency chain

1. Elementary CNF facts and the recursion for natural sum.
2. The finite-product rank lemma.
3. The finite profile order and matching characterization.
4. Well-foundedness, set-likeness, and N = profile rank.
5. The absorption lemma, proved for all positive auxiliary cuts.
6. Strict monotonicity of U under profile comparison, hence N <= U.
7. Published input: Lipparini's formula and minimality theorem for S.
   This gives S <= N because e-special strictness implies z-special
   strictness.
8. The independent finite-head lower bound from product ranks.
9. At a limit cut with successor last exponent: restore finite-offset heads
   one step at a time to obtain N >= S+k.
10. At a constant limit value with successor last exponent: arbitrarily many
    cut-sized heads force an extra omega; finite successors propagate it.
11. Apply the finite-head bound to get the full successor-cut lower bound.
12. The final limit-exponent case is already supplied by S <= N.

No constant-sequence formula is assumed in its own lower-bound proof.

## Conventions requiring care

- The strict relation in the rank proof uses the lower sequence's cut.
- d(a,b) is the unique ordinary-addition remainder solving a+d=b.
- A(t) is the *natural* product t tensor omega, not ordinary t*omega.
- At the middle limit case the weight is ordinary 1+d, not d+1.
- The finite correction counts exactly heads in [e,e+omega).
- Deleting the last monomial removes one copy, not the entire last CNF term.
- Exceptional heads form a multiset, retaining repeated equal entries.
- Minimal rank is zero; height is sup(rank+1).
- In the finite-head proof the designated constant-tail point need not be a
  greatest point of the e-strict sequence poset; the product-rank lemma
  applies at that point, which is all the argument requires.

## What validation did and did not do

The provided run reports 734,869 counted exact checks. They include
arithmetic identities, both absorption bounds, finite profile comparisons,
the correction formula, source regressions, and independent finite rank
calculations. Every recorded check passed. Some cases contain more than one
assertion.

The inequalities are tested symbolically, not with floating point. All test
ordinals have finite hereditary CNF below epsilon_0. The finite rank tests
compute predecessor ranks rather than defining the ranks by the proposed
formula. The prose proof—not the tests—carries the claim for arbitrary
ordinals and pointwise minimality.

There is no proof-assistant certificate, independent referee report,
exhaustive literature search, or claim of community acceptance in this
archive. These are explicit remaining verification tasks, not missing cases
within the stated conventional argument.

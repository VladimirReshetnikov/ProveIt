# Proof audit

## Mathematical status

The article contains complete English proofs, not a proof-assistant formalization.
The proposed results have not received independent peer review. Finite tests do
not certify infinite ranks. Literature-wide novelty and priority are unverified.

The main proof is independent of ProveIt's large-cardinal results and of the
predecessor report's maximal-order-type absorption theorem. The canonical
frontier representation and the uniform baseline are attributed to that report;
the representation is reproved here.

## Load-bearing statements

1. **No-resurrection (NR):** endpoint activity implies intermediate activity.
   This proves transitivity and forbids reuse of an earlier varying coordinate
   in a later chain block.
2. **Block realization:** each transition gets the largest capacity of a
   departing coordinate, or one when none departs. All other coordinates are
   zero. Terminal coordinates are handled separately.
3. **Leading coefficient:** departure counts `d` are finite longest-path counts;
   `c` also counts a possible terminal top-capacity block.
4. **Terminal region E:** the states with `d=c` form an upset and have no active
   label of the largest capacity. The induction removes a capacity level.
5. **Strict upper map:** natural sums of surviving high coordinates alone are
   insufficient. The lower-scale term includes kappa times finite state depth,
   followed by the lower-coordinate natural sum. It increases strictly at a
   same-leading-count state change, even when lower coordinates disappear.
6. **Attainment:** choose paths witnessing the departure counts and retain the
   predecessor states of the top-capacity deletion events. No-resurrection
   justifies the resulting skipped-state transitions.
7. **Pure lexicographic compression:** two order embeddings establish equal
   heights. They do not establish an order isomorphism or preserve point ranks.
8. **All-antichain representation:** maximal actual generators, not completed
   fibers, determine an exact state in the mixed finite/infinite skeleton.
9. **Phase refinement:** blocks are ordered phases, with a separate pure label
   for each positive-exponent phase. Direct substitution of impure capacities
   into the pure formula is invalid.
10. **Local ranks:** use the inclusive principal ideal, cap final shared
    coordinates at x+1, refine, and remove the final successor from its height.

## Boundary cases checked explicitly

- Empty state system: height 0.
- Empty underlying poset: its finitary-downset poset is a singleton, height 1.
- Coordinate-free finite systems: height is ordinary finite state height.
- Finite underlying poset with N points: finitary-downset height N+1.
- One ordinal chain: height of its finitary-downset poset is 1+alpha.
- An isolated omega^2 coordinate beside two successive omega coordinates:
  height omega^2, not omega^2*2.
- Two successor factors omega+1: product height omega*2+1.
- Reappearance without (NR): the raw proposed relation can fail transitivity.
- Coefficients and finite tails use ordinary addition; natural sums occur only
  where explicitly indicated in rank bounds or separate product checks.

## What is not claimed

No general ordinal-width formula, arbitrary finitary-powerset iteration theorem,
infinite-skeleton theorem, large-cardinal conclusion, automatic bound on lengths
of controlled executions, or exact pointwise equality of the first rank map R.
The notation engine covers only ordinals below epsilon_0, whereas the mathematics
allows arbitrary set ordinals. Complexity bounds in the article count ordinal
operations on an explicit state graph; they are not polynomial-time bounds in a
binary-encoded skeleton/CNF input.

## Evidence

`data/verification.json` records 129,593 finite assertions. The independent
local-rank record contains 940 finite systems, 6,132 point ranks and 37 symbolic
regressions. Direct finite-order enumeration checks the representation and local
rank routines. The transfinite upper and lower proofs are in the article.

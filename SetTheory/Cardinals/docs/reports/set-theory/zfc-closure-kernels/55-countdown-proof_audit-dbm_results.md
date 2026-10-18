# Difference-bound invariant search

The literal `Prog254.v` control graph was analyzed with difference-bound
matrices on its nine natural-valued registers and a distinguished zero.
Unlike independent `{0,1,>=2}` masks, this domain retains inequalities and
equalities between different unbounded registers. For example, the first
copy loop preserves `R6=R8`; later copy loops preserve `R1=R6` or
`R1=R6+1` at particular control sites.

| Extrapolation threshold | Worklist removals | Time, seconds | Invariant classes | Excluded guards |
|---:|---:|---:|---:|---:|
| 2 | 68,319 | 9.29 | 141 | 6 |
| 8 | 193,447 | 25.54 | 141 | 6 |
| 32 | 590,260 | 74.81 | 141 | 6 |
| 128 | 1,890,978 | 239.68 | 141 | 6 |

All four final invariants are bytewise equal at the level of class contents
and site-to-class indices. The exact excluded source guards remain
`8202, 8203, 8204, 8358, 8359, 8360`. Thus this experiment discovers no
additional unreachable whole instruction guard. It is not a proof that no
stronger invariant or machine reduction exists.

There are 698 control sites with a cross-register difference constraint
strictly stronger than the product of the individual variable intervals.
These constraints can still be useful for symbolic macro verification. If
two initially equal registers are tested later, their branch outcomes are
correlated. A checker that splits them independently may explore impossible
combinations. The DBM certificate can soundly rule those out.

The independent checker uses ordinary integer lists and its own closure and
affine-transfer code; the searcher uses NumPy. It checks all 6,460 source
sites, all 8,391 guards, all 8,384 enabled nonhalting transfer edges, initial
zero-vector inclusion, natural nonnegativity, canonical closure, and the
claimed impossible-guard list. All four certificates pass. No abstract-search
extrapolation rule is trusted by that final inductive-certificate check.

## Soundness argument

For a matrix D, let its concretization be all `x in N^9`, with `x0=0`,
satisfying `xi-xj <= Dij` for every finite bound. Floyd closure adds only
transitive consequences. A negative diagonal means an impossible inequality
`0<0` (in non-strict notation, `0<=-1`), so its concretization is empty.
Zero/positive decrement guards add their exact difference constraint;
increment and positive decrement translate the corresponding row and
column by plus or minus one. These are exact on difference-bound zones.

At joins, componentwise maximum contains both incoming concretizations.
Replacing a bound by infinity enlarges the set, and closure preserves it.
The search therefore constructs an overapproximation. Independently, the
finished certificate shows that the initial vector belongs to its initial
zone and that every feasible concrete successor belongs to the target zone.
Induction on the number of source steps establishes the invariant for all
reachable source configurations, without bounding register values or time.

For macro tests after a net offset delta, a zero test of logical register r
intersects the *original-value* zone with

`Rr <= -delta_r` and `-Rr <= delta_r`.

A positive test intersects with `-Rr <= delta_r-1`. Closure propagates these
constraints through every recorded equality/inequality. The source instruction's
own guard must be imposed before checking its binary macro. Physical register
indices must be translated using the actual permutation, not equated to
logical indices.

## Files

* `relational_dbm.py`: search and final transfer-inclusion check.
* `check_dbm_certificate.py`: separate integer-only certificate checker.
* `relational_dbm_threshold2.json` (and thresholds 8, 32, 128): final class
  certificates and exact source identity.
* `dbm_independent_check.json`: independent checker results.

The timing values are observations from this session and not complexity
bounds. All programs refer to the exact pinned source SHA-256
`1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746`.

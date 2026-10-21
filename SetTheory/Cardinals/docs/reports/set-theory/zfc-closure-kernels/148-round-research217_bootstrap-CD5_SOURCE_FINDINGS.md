# Source-side scope of the state-301 role

## Exact mapping

The eight state-51/right-zero decoder leaves are the two CD5 leaves in each
of four copies of the same destructive equality macro E. The first CD5 of
each copy uses the old state-301/read-0 role; the cleanup CD5 uses old state
88. Other CD5 leaves used for copying cache/parameters do not produce these
right-zero state-51 contexts.

- 4567/4572: AX tests c=b, with b=old cache+y. Equality clears the bundle top.
- 4585/4590: AX tests c=a, with a=old additive+x. Equality clears the bundle top.
- 4599/4604: NIP tests old cache h=1 and halts precisely when equal.
- 4708/4713: MP tests h=implication(top,additive+x).

These identifications agree with the inherited command contracts in
L2Root230.v and the literal current-source blocks. In particular, the AX
operands are ordinary natural parameters at the equality calls, not a
single restricted cache value.

## Sound reachable guards

The current 218 source has exactly the old source's ordered primitive list
and complete 4,744-vertex guarded control graph. The owned checker compares
both graphs and checks seed inclusion plus all 6,161 enabled edges of the
previous product invariant, rather than rerunning a broad fixed-point search.
Its five excluded edges and nonbottom halt annotation are retained.

The following facts therefore hold on every finite initialized source run,
without any consistency assumption:

- R3=0 at all four equality entries.
- At NIP entry R6=0; its initial increment makes the compared constant one.
- Inside the NIP cleanup, R6=0. This is the previously proved specialization.
- R5 remains abstractly unconstrained at all eight offending decrements.
  The invariant does not exclude either zero or positive branches there.

At the looped first NIP decrement, R6 may be zero or one, not always one.
No argument here assumes that the cache is not 1. The h=1 NIP case must remain
halting, including in the inconsistency direction of calibration.

## Exact current-layout costs of small guarded proposals

The owned incremental allocator was applied to the exact audited 218 source
and native table. These are literal raw graph prices with decoder-prefix
binding, not whole-machine correctness certificates.

1. Specialized NIP, retaining the exact h=0, h=1, h>=2 semantics:
   207 source subtrees, 4,738 leaves, raw 220 working states.
   It adds 303–306 and drops 53 and 68. The other three E copies remain, so
   state301 is still required.
2. Sharing-preserving NIP using a leading CD5 and the existing E:
   205 source subtrees, 4,744 leaves, raw 218 states.
   It adds303 and drops53. All four E copies remain. This is not a217 result,
   and old arithmetic roles of repurposed states still require checking.
3. Replacing the NIP zero-R6 equality cleanup by CB1:
   207 source subtrees, 4,742 leaves, raw220 states. It adds303/304 and drops
   nothing. Three other full E copies retain state301.
4. A fresh all-four-call proposal uses the common guard R3=0: transfer R5 to
   R3 using `(CD5,(CI3,CC2))`, then run E with register5 renamed to3.
   This is 207 source subtrees, 4,756 leaves, raw221 states. It does delete301,
   but adds303–306. Thus it solves the semantic role problem at an unfavorable
   physical cost, rather than yielding a217 candidate.

The fourth source contract follows by a direct decreasing-counter induction.
The transfer changes `(R5,R3)=(a,0)` to `(0,a)`, preserving R6 and all other
registers. Register renaming of E's all-natural theorem then clears R3 and
R6, returns normally iff a equals the original R6, and returns one break
otherwise. R5 stays zero. Thus the whole replacement has exactly E's effect
on every source-reachable entry satisfying R3=0, including its outward
control. It does not assume theorem soundness or Con(ZFC).

No full primitive runtime or blank-start proof was attempted for these raw
prices, because none reaches217 and each has explicit helper-role obligations.
There was no new broad source grammar enumeration.

Artifacts: `inspect_cd5_source.py`, `CD5_SOURCE_ROLES_AND_PRICES.json`, and the
four named subdirectories with exact source lists, raw tables and prices.

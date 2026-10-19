# Framework reduction experiments below 245 states

**Status: no machine below 245 states is certified by this work.** The two
smaller tables in this directory are explicitly named `unverified_scanner244`
and `unverified_scanner243`. They are diagnostic artifacts. Their successful
blank prefixes do not validate their recurrent execution.

The strongest negative execution evidence is now a **blank-reachable wrong
first clean source-control return**: the 244-state contraction reaches the
affected MP leaf at step 835,524 and returns with the wrong pointer at step
837,626. This does not settle its eventual halting or its possible equivalence
to consistency under a different source contract.

## Exact reference and reproduction

The reference is the old-label routed 245-state table in ProveIt commit
`6446ff5668307a2ac6aee1896037f0b792090389`, preserved in
`packages/zfc245-proof-20261018/certificate/machine_old.tm`. Its SHA-256 is
`f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267`.
The copy `base_old.tm` is byte-identical. It starts in old label 95, dispatches
in 96, and has the separate halt label 254. There are 245 working states.

After extracting the included reference ZIP to `packages/zfc245-proof-20261018`,
run from the archive root:

```sh
python3 framework_work/reproduce_findings.py \
  --reference packages/zfc245-proof-20261018 --full
```

The archive-level command `python3 -B code/verify.py --full` performs the
reference extraction automatically in a temporary directory.

Python assertions must remain enabled. `--full` needs a C++17 compiler and
repeats all three bounded mutation sweeps. Omitting it reproduces the exact
blank prefixes, literal discrepancy, complete symbolic scanner audit and
local state-166 search, and checks the retained sweep records.

All auxiliary Python scripts also honor `ZFC245_REFERENCE`; by default they
use the same archive-relative reference directory. `PASS_FINDINGS_REPRODUCED`
means only that these precisely scoped findings have been reproduced. It is
not a consistency-equivalence certificate for either smaller table.

## Source contexts and a blank-reachable discrepancy

`map_scanner_contexts.py` reparses the annotated 219-node `Dag254.v` and
relates it directly to the routed source by a closed segment bisimulation.
It checks 3,021 pointer pairs and 6,041 straight-line segments, comparing
the tested register and every register's increment count. The two source
compilations reorder some increments, so a bare leaf-order match is not
used. The 50 affected leaves consist of **49 in `axioms()` and one in
`mp()`**; counting decrement guards gives 97 AX and 2 MP obligations.
The complete source annotation paths are in `scanner-semantic-contexts.json`.

`reachable_scanner_discrepancy.py` records an exact finite observation on the
244-state contraction's own blank trajectory. At step **835,524**, it is in
dispatcher 96 at head -8, header 238, with physical registers
`(0,0,0,4,0,0,6,0,0)`, 233 spare blocks of value one, and source pointer
`1111000000`. This is affected source leaf 6367 in MP, a zero decrement of T.

| Execution from this same complete frame | Steps to first clean return | Residual pointer | Change in one-cell set |
| --- | ---: | --- | --- |
| Reference 245 | 2,044 | `111100001` | Add coordinate 0 |
| Contracted 244 | 2,102 | `1111001` | Add coordinate -2 |

Thus the wrong return occurs at absolute blank step **837,626**. The script
independently replays the full blank prefix and both fork endpoints with
sparse and dense tapes. `reachable-scanner-discrepancy.json` includes every
one-cell coordinate and declares all other cells zero. The clean return
criterion is exactly the one used by the earlier small synthetic witness:
dispatcher and head restored, sole left marker, clear source/header gap,
and the complete specified register-and-spare suffix unchanged.

A small additional source comparison rules out one immediate explanation
for this particular pointer difference: the two ordinary source executions
return to the root with different T values. The expected fork takes 652
source instructions and returns with logical registers
`(6,0,0,0,4,0,0,0,0)`; the altered fork takes 43 and returns with
`(6,4,0,0,4,0,0,0,0)`. These are ideal-source forks from the exact endpoint
configurations, not an assertion that all later binary steps follow the
ideal source. Different root files still do not establish different eventual
halting. A revised source contract or a stronger reachable-state invariant
has not been excluded.

## A bootstrap constraint can be relaxed

Delete old state 58 and change row `(41,0)` to `(0,L,84)`. This gives 244
working states. Deleting old state 41 as well and changing `(29,0)` to
`(0,L,84)` gives 243 states. Canonical tables, old-label tables and exact
renumberings are supplied for both.

Both altered machines reach a well-formed frame whose formula-bearing
registers `T`, `W` and `H` are zero. Two independent representations of the
tape, a sparse set and a dense byte array, agree on every nonzero coordinate.

| Table | Literal steps from blank | Head | Header distance | Logical register vector `(N,T,W,A,D,H,X,Y,L)` | Spare blocks, all value 1 | One-cells |
| --- | ---: | ---: | ---: | --- | ---: | ---: |
| Reference 245 | 407,915 | -5 | 181 | `(3,0,0,0,3,0,0,0,0)` | 167 | 351 |
| Unverified 244 | 818,324 | -8 | 245 | `(6,0,0,0,4,0,0,0,1)` | 233 | 488 |
| Unverified 243 | 1,389,062 | -8 | 331 | `(6,0,0,0,6,0,0,0,1)` | 321 | 666 |

The full one-cell lists are in `exact-blank-prefixes.json`. These finite facts
show that requiring the earlier exact bootstrap seed and all 54 inherited
grammar locks is stronger than necessary for searching a formula-clean
initial frame. A new grammar may change the bootstrap, provided its new
complete prefix and recurrent semantics are separately verified.

## The direct 244-state contraction has a concrete defect

The unchanged parametric instruction checker, with header distance `64+n`
for arbitrary `n >= 0`, processes all 8,391 guarded instruction obligations
for the 244-state contraction. It accepts 8,292 and fails 99. The failures
are the two branches of 49 decrement leaves and one increment leaf. Exactly
the 50 source leaves ending in six zero bits fail; there are no other
six-zero source paths. Distribution by physical register is:

| Operation | Physical register | Logical register | Failed guarded cases |
| --- | ---: | --- | ---: |
| Decrement | 2 | T | 70 |
| Decrement | 0 | W | 26 |
| Decrement | 1 | L | 2 |
| Increment | 2 | T | 1 |

`shorter58-full-failures.json` records each path, guard and checker error.
The per-case fuel is 1,000 symbolic rules. These 99 checker failures are
failures of a sufficient proof procedure; they are not individually promoted
to proofs of eventual behavioral inequivalence.

A separate literal computation demonstrates the actual scanner error. Start
at dispatcher 96, head 0, pointer

```text
11101001001000000
```

with header distance 64, all nine physical registers zero and one spare block
of value 1. Every tape cell not in the following set `C` is zero:

```text
C = {-1, 0, 1, 2, 4, 7, 10, 64, 66, 68, 70, 72, 74,
     76, 78, 80, 82, 84, 85}.
```

The reference machine's first complete return frame is at step 574, with
head 0, state 96 and one-cells `C union {15}`. This is the required zero
decrement successor pointer `1110100100100001`.

The contracted machine's first complete return frame is at step 650, with
head 0, state 96 and one-cells `C union {13}`. It therefore presents the
different pointer `11101001001001`. In its intermediate second dispatch,
at step 279, the head is incorrectly at coordinate 11. The corresponding
reference dispatch, at step 310, is at coordinate 0. This isolates the
scanner's false recognition of the internal zero suffix.

For this experiment a complete return frame means dispatcher 96 and head 0,
the unchanged complete register file at and beyond coordinate 64, the sole
negative one-cell at -1, and no one-cells in the pointer-padding interval
`[51,64)`. The original pointer tree has maximum depth 51. Both reported
return frames satisfy this definition. The script checks the first such
return and independently replays the stated endpoint with a dense tape.

The conclusion is exact disagreement of the first complete instruction
boundary. We do not claim that this source frame is reached by either blank
computation, that the contracted machine can never revisit the expected
frame later, or that its eventual halting differs from the reference.

## Broader local searches

The retained interval fixtures use header distance 181 and 167 spare blocks.
They contain 8,385 cases and exercise all 490 reference transition rows.
The reference's maximum fixture duration is 2,686 steps. The mutation screen
allows 20,000 steps and tape coordinates -64 through 1983 per case.

| Bounded search family | Recipes | Result |
| --- | ---: | --- |
| State-pair quotient, four selections of the merged read rows per unordered pair | 119,560 | 54 passed probes; zero full fixture survivors |
| One incoming edge retargeted, with its write and direction retained | 119,316 | 109 full fixture survivors |
| Combine surviving edge retargets to delete state 4 | 1,536 | Zero survivors |
| Combine surviving edge retargets to delete state 42 | 30 | Zero survivors |

This independent-edge search is strictly broader than a single pair merge.
For the retained individual survivors, only states 4 and 42 have alternative
targets for every incoming edge from another state. Their combined recipes
all fail the stated finite screen. Individual successful edits are not
assumed to compose: for example, apparent alternatives to the two incoming
edges of state 42 can use each other's original call to state 42.

There is also a bounded symbolic local search for eliminating pure router
166, whose only external incoming edges are `(143,0)` and `(250,1)`. The
known just-written bit is respectively 0 or 1. On initial head coordinate 0,
with predecessor bit `b` at 0 and written bit `c` at 1, its two transparent
steps reach coordinate 2 in states:

| Written bit c | Endpoint for b=0 | Endpoint for b=1 |
| --- | ---: | ---: |
| 0 | 53 | 49 |
| 1 | 54 | 90 |

Every other working state was tried as a replacement. The checker explicitly
branches on every newly encountered unknown tape bit, requires the exact
endpoint and complete tape preservation, forbids entering 166, and permits
at most 12 literal steps. Neither written-bit case has a replacement in
this bounded family. This does not exclude new routing states or longer
equivalences.

## Zero-five grammar search and next experiment

`anneal_routes_zero5.cpp` adapts the inherited routed grammar annealer. It
removes all bootstrap locks, uses objective `K + 0.25*bad`, and counts an
expanded syntax node as bad if its leading zero run exceeds five. Maximum
zero run six and maximum depth 64 remain hard constraints. Associations,
available-child cuts and folded-entry routes may change. The run resumes
from the verified 128-rule grammar.

Seed 710418 made 5,615,239 proposals in 600.006 seconds. The retained weighted
best checkpoint has 132 grammar rules, leading-zero depth 3, maximum zero run
6, source depth 45 and 11 bad nodes. It does not meet the zero-five target.
This is a heuristic checkpoint, not a lower bound, and the stochastic run is
not needed to reproduce the concrete scanner counterexample.

To repeat the heuristic, from this directory:

```sh
g++ -O3 -std=c++17 anneal_routes_zero5.cpp -o /tmp/anneal_routes_zero5
/tmp/anneal_routes_zero5 \
  ../packages/zfc245-proof-20261018/inputs/state_reduction/route-grammar.txt \
  ../packages/zfc245-proof-20261018/inputs/state_reduction/route-constraints.txt \
  zero5-new.json 600 710418 128 unlocked.txt zero6-resume.txt
```

Time-limited proposal counts vary with execution speed. A useful next search
would keep the exact source bisimulation and full runtime gates, but replace
the 54 fixed bootstrap equations with direct verification of the new
formula-clean blank prefix. A 128-rule zero-five realization would have the
desired 116 + 128 = 244 state accounting. This work establishes the validity
of relaxing the old bootstrap target as a search decision; it has not found
that grammar.

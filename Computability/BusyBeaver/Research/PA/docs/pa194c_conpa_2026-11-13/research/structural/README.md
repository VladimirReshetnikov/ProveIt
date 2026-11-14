# Bounded structural reduction searches

No construction with fewer than 194 working states was certified by these searches.
The package's accepted machine remains PA194C. `RESULTS.json` records exact
search families and counts. Empty JSONL result files mean zero accepted local
quotients in the indicated bounded family; they are not lower bounds.

## Two-sided local convergence

`macro_convergence.cpp` examines a stronger family than an immediate-successor
simulation check. An old configuration and its proposed replacement may each
execute up to 100 steps before reaching corresponding configurations. Every
intermediate cell read must stay inside the finite input window. The two tape
contents must match exactly at the join, subject only to the explicitly tested
encoding for the removed control.

Three encodings are examined: plain control identification, a two-cell head
shift when all external arrivals have the same direction, and a toggle of the
cell just written on arrival. The head shift and toggle can be combined.
For the last two encodings the incoming transitions are changed accordingly.
All unchanged controls relate by identical tape and head. Positive-duration
segments on both sides are required. The program also tries jointly changed
retained-control rows whose intermediate paths avoid the changed controls.

`pair_convergence.cpp` broadens the synthesis: for each deletion/encoding it
synthesizes both retained rows while allowing the same arrival changes. Its
recorded PA194 search considered 133,942 relations and 108,895,928 first-action
trials, with no survivor. The bound is 60 steps per side and radius 4.

The radius 6 abstract closure starts at the all-zero window in native state 74.
Each shift admits both possible bits at the newly exposed boundary; therefore
it overapproximates every blank-input run. A finer radius 4 context set comes
from every universal source-frame contract and the literal blank startup.
`symbolic_patterns.py` includes the internal configurations of unary sweeps and
of the four generic list lemmas; it does not omit the arithmetic block controls.
Variable lengths, list contexts, and opaque surroundings are conservatively
expanded. This yielded 12,393 state/windows for PA194 and 12,282 for PA194C.

The recorded scans found zero quotients for both machines. These tests establish
only the stated bounded negative results. They neither settle state minimality
nor replace the consistency calibration.

From the package root, representative replays are:

```sh
g++ -std=c++17 -O3 research/structural/macro_convergence.cpp -o /tmp/pa_macro_search
/tmp/pa_macro_search research/structural/inputs/pa194C.native.tm 6 100 - all
/tmp/pa_macro_search research/structural/inputs/pa194C.native.tm 4 100 research/structural/194C_symbolic_patterns_k4.txt all
g++ -std=c++17 -O3 research/structural/pair_convergence.cpp -o /tmp/pa_pair_search
/tmp/pa_pair_search research/structural/inputs/pa194.native.tm 4 60 research/structural/194_symbolic_patterns_k4.txt
```

To regenerate the universal context sets, run `python3 research/structural/symbolic_patterns.py --family 194`
or use `--family 194C`. The extraction
can take several minutes. Assertions must stay enabled.

## Shorter return scanner: rejected direct deletion

Removing native 34 and changing `(23,0)` to `(0,R,75)` shortens the zero-run
recognizer by one control. It fails 113 universal primitive-instruction outcomes
for each machine: 113/4780 for PA194, and113/4749 for PA194C. Failure records are
included in `scanner_delete34_194.json` and `scanner_delete34_194C.json`.

The obstruction occurs outside the AX emitter as well as inside it. In
particular, the recurring entry at source site 25 fails. Thus tightening only
an AX grammar's zero-run score does not justify the deletion. These failures
reject the inherited local simulation contract; they are not advertised as
blank-input halting counterexamples for the altered machines.

Replay: `python3 research/structural/scanner_test.py`.

## A source rotation whose physical implementation remains open

At the source level, replace

```
node170 = (node36, node169),  node36 = (node28, node35)
```

by `node170 = (node28, (node35,node169))`. This shortens PA194's recurring
site 25 path from 100000 to 10000. Without another change it redirects the
continuation at source 3660 from 25 to 34. Retagging the right leaf of node166
from `continueTo3` to `continueTo4` restores the entire resolved instruction
graph, exactly. The new continuation path is1011011.

This is a source-level result. It is not a 193-state physical construction.
The four ordinary reader-row changes are straightforward, but the affected
physical shortcut at native 18/read1 no longer implements the required return.
Testing all 776 possible replacement actions for that one row found none
satisfying the universal contract for the new continuation.

A separate finite local screen tries `(18,1)=(0,L,n)` and one additional row
change. Of 1,608,648 local action trials, 2,006 repair the concrete suffix.
Of these, 1,308 alter a control in the imported arithmetic-block protection set
and are excluded from the oracle-based validation route. They are **unverified**,
not proved impossible. The other 698 all fail universal source contracts.
No physical implementation of the rotated source is accepted here.

Replay the source identity and one-row search with:

```sh
python3 research/structural/rotate_continue.py
```

The concrete screen and universal filtering are deliberately separate:

```sh
node research/structural/cc4_local_synthesis.js
python3 research/structural/cc4_two_row_filter.py
```

The concrete screen keeps all reads in cells -8 through 20 and uses a 100-step
bound. It is useful for proposing mutations, not for claiming their correctness.
The subsequent universal filter protects the assumptions of the inherited
arithmetic-block oracle and records the first failed contract for each examined
candidate.

## Reproduction inputs and scope

`inputs/pa194.native.tm` has SHA-256
`e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54`.
`inputs/pa194C.native.tm` has SHA-256
`b35d80b01ce9c2e95c8b29222881f40928247cdeffac322e4643f4f6694cd33c`.

The Python runners use the frozen, attributed PA194 sources in
`reference/pa194`, and the accepted PA194C table and source maps at the package
root. They do not modify the accepted machine. Search outputs and timing fields
can be regenerated in this research directory.

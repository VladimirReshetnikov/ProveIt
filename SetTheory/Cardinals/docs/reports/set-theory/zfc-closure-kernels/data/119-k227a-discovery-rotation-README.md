# Discovery record for the 227-state candidate

The authoritative final machine and its complete verification are in the parent
package. These files preserve one informative failed construction and the exact
successful search hit. They are research history, not an additional trusted
premise for the final construction.

## A smaller source DAG that failed

`failed_seven_zero/` contains the exact earlier 227-state prototype, its logical
source in JSON and text, the closed-rotation receipt, and the finite counterexample.
Starting from the verified 228-state basis, closed left rotation 98/74 reduced the
source DAG from 212 to 211 nodes and maximum depth from 40 to 39. Its complete
source guarded graph was unchanged. However, six source paths acquired seven
consecutive zeros. The binary finite filter rejected this particular prototype:

| Field | Recorded value |
|---|---|
| Source index | 40, counting from zero |
| Instruction | `CD 1`, zero branch |
| Program counter | `111010010010000000` |
| Previously completed guarded cases | 56 |
| Transitions before rejection | 658 |
| Observed state and head | 96 and 0 |

The failure shows why source graph equality and source DAG minimization alone
were insufficient. It does not establish that every source with a seven-zero
path fails. `discovery_failed_seven_zero.json` records the exact table and source
hashes and makes this distinction explicit.

With the parent package's finite filter compiled, the failed input can be replayed
as follows, using inherited machine labels:

```sh
finite_filter failed_seven_zero/candidate.tm failed_seven_zero/sites.txt 0 0 5121 6656
```

## The successful search hit and its simplification

`successful_discovery/` preserves the exact 227-state table found by the repair
search and its source. Its finite profile with all primary registers zero passed
all 6,656 guarded cases. The accompanying history starts after the initial failed
prototype; it is not a complete standalone construction script.

The search used a temporary fresh state 300 and eventually folded states 74/242.
Inspection then removed the unnecessary historical complexity. Renaming state 74
to 242 and state 300 to 74, with every other state name fixed, gives exactly the
clean final inherited table. `discovery_isomorphism.json` checks all 454 rows,
preserves the start and halt labels, and confirms equality of all 5,121 source
leaves. The successful discovery table hash is
`27578163b92a80c21af63c2b53b8a89e2f85dad8dac49a5ab8c508d795b0e959`;
the clean inherited table hash is
`175d6d4df7b988b45253e0a3bcb2651648b55a0ca1efddd4d5c6100ff71b8f46`.

The clean construction requires just one closed right source rotation, 184/181,
followed by a context split that deletes state 218. It introduces no fresh state.
The rotation makes original state 179 arrivals carry a zero immediately left of
the head; original state 242 arrivals carry a one there. State 218's incoming
transitions already record their context in that same tape bit. Its left-zero
context can therefore share state 242, and its left-one context can share state
179. Existing helper states 165, 195, and 215 implement the required actions.

The separate local checker proves eight exhaustive two-cell macro cases and
checks all 450 ordinary basis rows. Each macro preserves both inspected tape
cells, advances the head one cell, and takes between one and five transitions in
the new table. Its proof applies to every binary tape from the common start
state. The source rotation and the final universal binary runtime are certified
separately in the parent package.

## A short subsequent search for 226 states

Two heuristic walks considered 17,489 and 11,390 distinct table layouts within
their respective runs. Temporary state growth, exact duplicate merging, source
reassociation, and tagged folds produced thirteen 226-state tables; all thirteen
failed the finite runtime filter. The second walk protected low numbered decoder
states to reduce interference with borrowed arithmetic transitions. The search
then stopped for final artifact verification and packaging.

`optional226_search_summary.json` preserves the aggregate counters. The sets of
layouts may overlap across runs. These negative results establish no lower bound
and make no claim that 227 is optimal.

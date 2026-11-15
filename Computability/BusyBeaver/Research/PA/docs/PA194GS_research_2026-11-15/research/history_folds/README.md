# Generalized history folds: finite negative search results

No construction below 194 states was obtained by these searches. The thirteen
new incoming 194-state designs and the gate-reassociation candidate resisted the
specific local transformations recorded here. These results do not establish
a lower bound on machine size or completeness of the wider design space.

## Completed work

| Search | Inputs | Bounds | Result |
|---|---|---|---|
| Noncircular history folds | All thirteen newest incoming 194-state designs | Radius 7; at most 31 child steps per old step | Zero merges |
| Noncircular history folds | The same thirteen designs | Radius 9; at most 129 child steps per old step | Zero merges |
| Circular history folds | The same thirteen designs | Radius 8; at most 31 child steps per old step | Zero merges |
| Noncircular history folds | Gate-reassociation 194-state candidate | Radius 9; at most 129 child steps | Zero merges |
| Two-sided common futures | H5XS and the gate-reassociation candidate | Radius 7; 1–3 old steps and 1–15 child steps | Zero merges |
| Iterated noncircular closure | Unfolded ORH201 | Radius 7; fuel 31 | Exhausted all 192 rooted graphs in this closure; minimum 194 |
| Iterated noncircular closure | Unfolded MP201 | Radius 7; fuel 31 | Exhausted all 192 rooted graphs in this closure; minimum 194 |
| Iterated closure, breadth first | Unfolded H5XS204 | Radius 7; fuel 31; 5,000 processed graphs | Budget limited: 6,600 seen, 1,600 queued; minimum 197 |
| Iterated closure, depth first | Unfolded H5XS204 | Radius 7; fuel 31; 5,000 processed graphs | Budget limited: 5,045 seen, 45 queued; minimum 194 |

The two H5XS searches **did not exhaust their queues**. Their different minima
reflect exploration order, not a state-count obstruction. No 193-state result
was found in either run. The overlapping batches must not be summed as distinct
machine counts.

Each thirteen-machine noncircular batch screens 3,934,320 row-action instances:
302,640 per input. The circular batch covers all 18,721 unordered control pairs
per input; 15,181,260 pairs of replacement actions passed its permissive filter
and received the final literal check. The common-future runs checked 1,133,377
joint action pairs for H5XS and 1,202,033 for the new gate construction.
The separate radius-9 gate run admitted 10,650,383 finite contexts.

The positive control on unfolded AX11H201 recovers the seven known fold pairs,
with eight action choices. It was also rerun through the packaged runner. This
checks that the search detects existing contextual folds; it does not turn the
negative searches into a general lower bound.

## What is checked

A radius-r context consists of the parent control and the 2r+1 bits centered at
the head. Starting with the blank context, the closure applies each parent
transition and inserts **both** possibilities for the newly exposed boundary
bit. Consequently it is an inductive overapproximation of every context on the
blank execution. Unknown exterior bits are not treated as blank.

Each candidate simulation tracks the full retained window, head displacement,
and control. It refuses to read outside the retained window. Thus every changed
cell is included in the comparison, and the untouched exterior agrees. Both
clocks must be positive. A successful finite certificate of this kind can give
primitive-recursive witness maps between halting computations; none of these
checks depends on assuming PA is consistent.

`noncircular.cpp` tries all write/move choices and target controls or halt for
each source row, followed by unchanged parent transitions. It records the
interior controls and combines compatible options for each proposed merge.
Options using either merged control in the interior are excluded. It then
rechecks the actual quotient literally. Its precomputation is a restriction:
merges that require target aliasing before the precomputation, or circular
routes, need not be represented. The term "exhausted" for its closure means
exhaustion of this recorded search relation, with rooted graph deduplication
and native start 74 retained.

`recursive_folds.cpp` permits returns to the merged control. Its permissive
per-bit filter admits such returns; the final check uses both actual replacement
rows and enforces the stated positive clock. This solver was supplied in the
ORH packet and is included unchanged. The source packet had run it on PA194OR
at radius 6/fuel 64; the new batch here uses radius 8/fuel 31 on all thirteen
newest designs.

`commonfuture.cpp` permits 1–3 parent transitions and 1–15 child transitions
before a common configuration, with circular routes allowed. This is distinct
from both an expansion of exactly one old step and the separate shortcut
search that compresses an old computation into exactly one new step.

`fold_closure.py` iterates the noncircular search and deduplicates rooted action
graphs. ORH201 and MP201 each have layer counts 1, 8, 27, 50, 55, 36, 13, and 2
for 201 down to 194 states. All graphs in both completed closures retain a
spanning root at native start 74. One ORH194 leaf is absent from the reference
census but differs by only a three-step detour; it is not offered as the
materially different design requested by the user.

## Files and reproduction

`results.json` gives the final numerical summary. `receipts/` contains the
captured outputs and compact closure results. The full intermediate graph
ledgers and thousands of temporary tables are omitted; their original receipt
hashes are recorded, and the supplied driver regenerates them. Command prefixes
in the historical batch receipts were made relative during packaging; stdout,
stderr, outcomes, and input hashes were not changed.

`SOURCE_TABLES.json` binds all eighteen native inputs to SHA256 hashes and source
locations. Thirteen entries form the incoming batch; the other five are the
gate candidate and unfolded positive-control/closure inputs. These are literal
two-symbol tables with native start 74 and halt 254. They must not be run from
state 0. The package's main dense machine has a different, explicitly supplied
start convention.

Only a C++17 compiler and Python 3 standard library are needed. From this
directory, compile the engines:

```sh
g++ -O3 -std=c++17 noncircular.cpp -o noncircular
g++ -O3 -std=c++17 recursive_folds.cpp -o recursive_folds
g++ -O3 -std=c++17 commonfuture.cpp -o commonfuture
```

Replay the three batches and the positive control:

```sh
python run_batch.py --engine noncircular --radius 7 --fuel 31
python run_batch.py --engine noncircular --radius 9 --fuel 129
python run_batch.py --engine recursive_folds --radius 8 --fuel 31
python run_batch.py --engine noncircular --radius 7 --fuel 31 --cases AX11H_raw201
python run_batch.py --engine noncircular --radius 9 --fuel 129 --cases Gate194
```

The output defaults to `reruns/`, leaving archived receipts intact. `--output`
and `--jobs` are available. Circular and common-future searches take longer
than noncircular precomputation. Replay the two common-future runs:

```sh
./commonfuture inputs/PA194H5XS.native.tm /tmp/h5xs_cf 7 3 15
./commonfuture inputs/Gate194.native.tm /tmp/gate_cf 7 3 15
```

Replay the complete and budget-limited closures:

```sh
python fold_closure.py inputs/ORH201.native.tm ORH201
python fold_closure.py inputs/MP201.native.tm MP201
python fold_closure.py inputs/H5XS204.native.tm H5XS204_BFS --strategy bfs --max-nodes 5000
python fold_closure.py inputs/H5XS204.native.tm H5XS204_DFS --strategy dfs --max-nodes 5000
```

The closure driver imports only the package's `../../comparison/census.py`
pure table routines. It records missing-start exclusions and nonspanning
outputs explicitly. It requires a fresh output ledger rather than resuming an
old queue. The two H5XS runs are intentionally finite budgets, not commands
promising exhaustive completion.

## Attribution and claim boundary

`SOURCE_CODE.json` records code hashes and provenance. The circular solver is
copied from the supplied ORH research packet. Preserve the ProveIt, James Chang,
and Wade notices supplied under `../../licenses`. The noncircular search,
two-sided common-future extension, closure driver, and new run receipts were
created during this task.

These experiments are independent evidence about explicit finite search
families. They do not complete the inherited arithmetic calibration or the
unfinished Lean endpoint. Structural novelty of the new gate design is checked
separately by `../../verification/check_novelty.py` against the packaged pinned
comparison corpus.

# Bounded searches for further state folds

**Result:** the recorded search found no surviving local fold in its specified family. This is a bounded synthesis result, not a lower bound on the number of states and not an impossibility theorem for a 214-state machine.

The 32 tables in `inputs/depth44_45/` are **earlier physical-rotation synthesis tables**, associated with source depths 44 (seven tables) or 45 (twenty-five tables). **They are not the final depth-41 machine.** Their role here is to reproduce the negative search; they are not individually presented as accepted ZFC-consistency machines. The final deliverable remains `../../machine/k215r.native.tm` and its separately reviewed source and runtime.

## Exact scope and result

| Parameter | Recorded setting |
|---|---:|
| Input tables | 32 |
| Working states in each input | 215 |
| Backward graph-context depth | 4 transitions |
| Eligible state-pair/read-bit specifications per table | 74–81 |
| Replacement actions per eligible pair | 860 |
| Maximum microsteps per symbolic branch | 45 |
| Maximum symbolic nodes per local block | 200 |
| Total candidate specifications tried | **2,149,140** |
| Surviving specifications | **0** |

A pair is considered only when its other read-symbol row is literally identical and its graph-derived tape-context families are distinguishable. For the changed row, the search tries both write symbols, both directions, and every one of the 215 existing working-state targets. It redirects the removed state to the retained state throughout the proposed table.

The local checker compares one old transition with a proposed finite microblock. It accepts an endpoint only when the control state, head displacement, and entire tape change match the old transition under the proposed state identification. Unknown initial tape bits are branched over; modified cells must be restored exactly. An early halt is rejected. A step or node limit means that this local proof attempt did not close; it is not a semantic counterexample.

Backward contexts are computed from transition-graph histories: read guards filter inconsistent histories, writes update known tape bits, and head movement changes their coordinates. At depth zero or the initial state, the remaining tape is unconstrained. This gives a finite over-approximation of possible tape contexts, rather than a bounded blank-run trace.

The scope excludes other source programs, other encodings, arbitrary multirow rewrites, longer helper blocks, deeper contexts, and the final depth-41 table. The fact that none of these bounded specifications survived therefore cannot establish global optimality.

## Controls

`reports/controls.json` records fresh controls of the portable script:

- Unfolding the accepted 69/400 marker construction yields the known fold; both origin cases close in exactly three transitions.
- A deliberately early halt is rejected.
- The superficially attractive 8/127 fold through helper 110 is rejected for both origins. That helper revisits the proposed folded states and creates a cycle. Finding a selector in the old graph alone does not validate a fold.

These controls check concrete positive and negative behaviors of the local filter. They are not an exhaustive proof of its implementation.

## Evidence and reproduction

`reports/earlier_rotation_fold_search.json` contains every input hash, eligible pair, specification count, and result. It also identifies the historical script. `reports/portability.json` checks that all core function bodies in the portable script have exactly the same Python abstract syntax trees as the actually executed research script. Only the command-line interface, output paths, metadata, and input checks were changed. The historical driver is preserved in `provenance/`.

`reports/portable_smoke.json` is a fresh portable replay of the first input; its eligible pairs, count, and empty survivor list agree with the recorded search. The full 32-table search was not rerun solely for packaging.

From the packet root, reproduce the controls with:

```bash
python3 -B research/encoding/check_controls.py \
  --baseline baseline/k215.native.tm \
  --output research/encoding/reports/controls-fresh.json
```

Reproduce one table's bounded search with:

```bash
python3 -B research/encoding/search.py \
  research/encoding/inputs/depth44_45/candidate000.tm \
  --output research/encoding/reports/candidate000-fresh.json
```

The recorded limits are defaults. To state them explicitly, add `--depth 4 --steps 45 --nodes 200`. Repeat the command for the other numbered input tables to reproduce the full family. The scripts use only the Python standard library and require assertions enabled.

## Attribution

The original machine, compact calculus, compiler, calibration, and prior folding constructions retain their inherited ProveIt attribution and licenses. The parallel source-search task produced these earlier rotation tables. The encoding task authored the context-based local search, its controls, and this bounded negative-result package. No source-state-count lower bound or new accepted machine is contributed by this directory.

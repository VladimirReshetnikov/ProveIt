# Physical decoder rotations and auxiliary-frame screens

These are discovery programs, not final proof checkers. Their completed runs found no surviving local fold, and no 218-state construction follows from them. Logs and `search_summary.json` distinguish completed searches from partial progress logs.

The `rot_full.py` and `rot_alias.py` copies have one portability edit: their original absolute import path was removed. Set `PYTHONPATH` to the pinned K221 `portable` directory extracted by the main replay. The algorithms themselves are unchanged. The other rotation modules use only the standard library, plus these pinned modules where imported.

For example, after the main replay has populated `../fresh-replay/inputs`, from the packet root:

```bash
export PYTHONPATH="$(pwd)/../fresh-replay/inputs/K221_Construction_2026-10-20/portable"
python3 -B research/encoding/physical/full_search.py \
  machines/rho6_219/native.tm machines/rho6_219/sites.json \
  ../rho6-rotation-search 2 7 8 11
```

The arguments following the output directory select depth, permitted maximum zero run, invariant radius, and bounded matching steps. This is an example invocation; discovery logs are evidence for their recorded completed table counts, not an assertion that all choices of search bounds yield the same run.

`rot_full.py` uses the actual decoder mapping and admits the asymmetric source condition `break(A)=0, continue(C)=0` for `((A,B),C) <-> (A,(B,C))`. It can reuse a pre-existing physical state for the new middle subtree. `rot_alias.py` allows multiple source roles of one physical decoder state and checks all corresponding occurrences together. `inv_fold.py` supplies an inductive finite-window overapproximation; `sim_fold.py` checks a bounded local matching path. All hits would require fresh complete runtime and source proofs.

The source-level mathematical admissibility of a reassociation does not prove a physical rewrite correct: helper routines may use address bits to the left of the current decoder leaf. The final delivered machines are validated separately by the portable unbounded replay.

`context_fold.py` and `random_walk.py` are historical snapshots and may retain workspace-specific input paths. Adapt those paths before rerunning. Their logs must not be interpreted as exhaustive impossibility results.

## Auxiliary-frame fold screen

`auxiliary/weak_merge.cpp` is a standalone C++17 program. It accepts a native table, a plain-text source leaf list, and an output file. Convert each JSON source row `[path,opcode,arg]` to one text line `path opcode arg`, using `-1` for the `CH` argument. Compile with a C++17 compiler. The program tests pair folds with one common transition and one synthesized transition, on small concrete primitive frames.

The endpoint permits any well-formed nonempty spare list, any head translation and gap of at least 64, but requires the exact logical counters and expected source PC. The baseline, inert-insertion, and rho6 logs report 227,592, 229,336, and 228,464 attempted candidates respectively, with zero survivors. These are finite rejection screens; a survivor would not be a proof of correctness.

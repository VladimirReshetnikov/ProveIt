# Bounded source packing and allocation research

These are research inputs and negative search receipts. **No new binary
candidate is accepted here.** The main verified CM215 is under `../../machine/`.

The four source beams examined 801, 94,227, 69,868, and 106,432 distinct source
trees respectively. The best source DAG count remained 202. The latter two
used the score `DAG nodes + 2 * maximum_zero_run`, with best value 214 =
202 + 2*6. This score is not a Turing-machine state count. Every saved source
was checked for exact ordered primitive word and complete guarded ordinal
CFG agreement with the accepted K215 source.

`runs/*/summary.json` retains the original run metadata and all finalist
hashes/metrics, plus the SHA-256 of the original detailed receipt. Large
repeated intermediate subtree dumps have been omitted. Each run's first
finalist is included; the four partial-selector finalists used for allocation
are included as well. Counts are observations from bounded runs, not lower
bounds. Time-capped reruns can explore different numbers of trees.

`rotate_closed.py` retains the whole partial selector. `rotate_partial.py`
retains its two used branches and selector-frame intervals. `rotate_open.py`
permits `(A,(B,C)) <-> ((A,B),C)` when A has no escaping forward jump and C
has no escaping backward jump; B may be open. `rotate_unfrozen.py` also
allows changes inside the two used branches, while retaining the three
selector intervals. Both complete CFG readers remain acceptance conditions.

From the packet root, a bounded optional search is:

```sh
python3 -B research/source-packing/rotate_open.py \
  --source reference/primary215/sites215.json \
  --baseline reference/primary215/sites215.json \
  --output /tmp/cm215-open-search --seconds 45 --beam 128 --rounds 100
```

The output directory must not exist. The search tools use only Python's
standard library. Their emitted detailed receipts can be large.

`allocate.py` and `allocate_stride2.py` use NumPy/SciPy's mixed-integer
optimizer. These optional tools are **not** needed by the main verification
entry point. Existing protected engine rows are an inherited synthesis
filter; no current whole-machine theorem follows from satisfying this model.
For example:

```sh
python3 -B research/source-packing/allocate.py \
  --source research/source-packing/runs/partial/candidate00.json \
  --output /tmp/cm215-partial-allocation --limit 30
```

The first stride-two allocation had eight changed roles with seven usable
existing role slots and was infeasible under that model. Other global
allocations and the direct 61-leaf command remain open. The receipts under
`allocations/` retain the exact domains and solver result. The unchanged
baseline was a positive prefix-binding control; it is not a newly derived
machine.

The packaged search scripts differ from the executed versions only in local
input/dependency paths, recorded in `packaging_changes.json`. Vendored source
and decoder utilities retain upstream attribution. The root packet's notices
and licenses apply. Stored receipt paths identify the original run and are
not required to exist on the reader's computer.

Recheck the supplied literal finalists without searching or an optimizer:

```sh
python3 -B research/source-packing/check_saved.py
```

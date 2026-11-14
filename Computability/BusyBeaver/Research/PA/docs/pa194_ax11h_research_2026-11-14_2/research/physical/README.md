# Physical reduction screens for PA194, AX11H194 and QAX11H194

These are **negative bounded synthesis results**, not lower bounds and not
consistency proofs. No sub-194 blank-start machine was established by these
searches. The new AX11H194 and QAX11H194 tables are included as exact search
inputs; their construction and logical evidence belong to the enclosing report.

## Findings

For each of the three 194-state input tables, the screen found no compatible
merge among all 18,721 unordered pairs of controls. It then found no compatible
head-displaced merge among 32,038 ordered pairs whose removed control has a
single incoming movement direction. The latter family allows changing both
rows of the kept control and reversing the movement into the removed control.

Both searches require every recorded local tape window to recover the mapped
endpoint of one old transition, preserving every local tape cell, within 100
new transitions and without stepping outside the radius-four window. The
programs allow revisits to the new merged state. Initial controls are included;
when the removed control is initial, blank-tape translation supplies the fixed
head displacement. None of these restrictions is asserted necessary for an
arbitrary successful state reduction.

The three recorded window collections contain 10,886, 10,909 and 11,018
state/window pairs respectively. They combine symbolic source execution,
explicit scan interiors, physical arithmetic samples, and the exact finite
blank startups. The physical sample is 3,000 deterministic pseudorandom register
files plus 121 uniform/single-coordinate files, with 27 block executions per
file: 84,267 block runs. Register values range from 0 through 10 and file lengths
from 10 through 13. This sampling is deliberately **not** represented as a proof
that all arithmetic contexts are covered. Symbolic exterior windows can also
be conservative overapproximations. A negative result here rules out only the
precisely recorded finite-window requirements, not reductions justified by
stronger global invariants or by different simulations.

The ordinary merge and neutral-row synthesizers are retained from the prior
PA research. The head-displaced synthesizer, arithmetic-context extension and
hybrid runs are new work in this investigation. Attribution and upstream
licenses are retained in `licenses/`.

## Why the familiar 193-state splice still fails

Applying the old runtime splice to either new hybrid means identifying native
301 with 88, setting 88/0 to `0 L 51`, and setting 51/0 to `0 R 122`.
Both resulting 193-state tables, from native start 74 on blank, reach

- control 35;
- head position 14;
- exactly two one-cells, at -3 and 1;
- after exactly 92 transitions.

The row 35/0 writes 1, moves right, and remains in 35. Hence each run continues
forever into blank cells to the right. This is an explicit ray certificate,
not timeout extrapolation. Full finite traces are in
`results/rejected_hybrid193_startups.json`. Independently replay them with
`python3 replay_startup_rays.py`. The new H or AX11 modifications do
not repair this startup failure.

## Reproduction

Python 3 and a C++17 compiler are sufficient for replaying the frozen-window
searches, without a repository checkout or network:

```
python3 replay.py --out replay-output
```

The script checks all input hashes, compiles the two synthesizers, reruns all
six ordinary/displaced searches, and compares exact counters and zero-hit
outputs with `results/summary.json`. Timing values are not compared.

`code/collect_contexts.py` is the exploratory context generator. Its CLI is:

```
python3 code/collect_contexts.py TABLE SITES INSTRUCTIONS OUT RADIUS RUNTIME STARTUP_STEPS
```

Here RUNTIME is the attributed `symbolic_runtime.py` provided with the machine
construction, and SITES/INSTRUCTIONS are its generated source arrays. The native
labels, start 74, source frame control 84, original physical register order,
and final startup head -2 are explicit assumptions. For the hybrid recorded
screens, primary arithmetic-engine windows were reused only because their
engine rows agree; hybrid exterior windows and startups were regenerated.
Running the full collector independently on a hybrid may produce a slightly
smaller engine envelope because it does not union in primary exterior contexts.
The frozen inputs, not a claim of canonical context generation, define the
replayed synthesis experiment.

A further staged screen applies each locally neutral one-row candidate to
QAX11H194 and then reruns the ordinary pair-merger. These are candidate screens;
the old window set is retained after the first edit. All 358 stages completed with zero hits;
the exact totals are in `results/staged_summary.json`. Neither neutral closure on these
windows nor a search hit would by itself establish a correct blank machine.

For the optional staged replay, use:

```
python3 staged_replay.py --out staged-replay-output --jobs 4
```

This first regenerates and byte-compares the 358 neutral proposals, then checks
each saved pair-merger counter and the absence of hits. The first-stage local
simulator rejects a proposed detour if it revisits its changed control before
recovering the original one-step endpoint. The second-stage simulator allows
revisits to its new merged control. Both use the same frozen radius-four
windows and a 100-step local bound. Retaining old windows after the first edit
is part of the screening definition; no invariant for the mutated table is
silently assumed.

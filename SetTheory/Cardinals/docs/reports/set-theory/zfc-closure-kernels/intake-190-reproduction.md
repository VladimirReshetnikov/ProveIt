# Recovering and replaying the contextual 218-state alternative

From the repository root, choose new paths outside the repository:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake190.py /tmp/ctx218-recovered
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake190-fresh-k218/prepare.py --packet /tmp/ctx218-recovered/K218_Contextual_Alternative_2026-10-20/K218_Construction_2026-10-20 --output /tmp/ctx218-direct
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake190-fresh-k218/run.py --work /tmp/ctx218-direct
```

The outer recovered directory follows the distinct archive name; its internal
wrapper deliberately keeps the older construction name. Recovery restores all
102 members and executes nothing. The [placement map](data/intake190-placement.json)
accounts for every original/alias. It also preserves the nested predecessor
and separate membership-obstruction supplement, including their TeX/PDF files.

Preparation copies the package to fresh scratch space and extracts only the
selected pinned runtime dependencies. It writes the six-job direct plan:
source proof, complete table lineage, canonical/dual startup, independent
startup audit, full final runtime, and independent runtime audit. The heavy
runtime has a 240-second process cap; other leaves have 60 seconds. Assertions
remain enabled. The final selected status is `FRESH_DIRECT_LEAVES_PASS`.
This is not the delivered wrapper's omnibus status or recursive ancestor replay.

The [actual record](data/intake190-fresh-k218/execution/result.json) and
[review](data/intake190-fresh-k218/review/review.json) bind all six passes, 6,167 cases,
1,514,325 symbolic steps, minimum duration 13, all 436 rows, and exact
312,701-step startup. Eleven artifacts reproduce byte-for-byte. Only elapsed
time differs in runtime metadata. The first own preparation-path failure and
its correction are retained; no supplied checker was changed to obtain a pass.
Portable preparation was tested for normalized-plan equality with the actual
run. Full runtime ran once.

No supplied wrapper, manifest validation, ancestor verification, research
searches, Coq/Rocq, or Lean is invoked by these commands. The supplement's
finite model and all-natural induction are separate mathematical evidence;
its wrapper is not needed for the machine. The [intake](intake-190.md),
[independent proof review](intake190-source-review.md), and
[candidate publication](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/contextual/README.md)
explain the remaining exact-table formalization limits and the row157 variant.

# Recovery and selected reproduction for batch 193

Restore both original archives into a new directory outside the repository:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake193.py /tmp/intake193-recovered
```

This executes no supplied code. The tested [recovery receipt](data/intake193-recovery.json)
records 111 members for Source 153 and 433 for Source 154. Placement
`ff23f24af8` retires both ZIPs; the [map](data/intake193-placement.json)
retains every original, alias and archive-only article/PDF. Source 153 is
`ZFC_218_Research_2026-10-20 (1).zip`; Source 154 has no `(1)` suffix.
Their identical inner folder names must stay in separate extraction roots.

Use Python with assertions enabled. Selected checks always use a disposable
copy or new output directory, and must not overwrite delivered evidence.
No instructions here invoke manifests, ancestor suites, broad searches,
old full runtimes, Lean or Rocq.

## Source 153: six leaves

Follow the [portable selected guide](code/intake193-source153/README.md).
Its `--packet` argument should point to:

```text
/tmp/intake193-recovered/ZFC_218_Research_2026-10-20 (1)/ZFC_218_Research_2026-10-20
```

Quote that path in the shell. The guide selects exact maintained K219 table
and source inputs, six reviewed commands, 120-second bounds, and an independent
saved-record audit. The source-reviewed path adapter was not the runner used
for the original execution; its exact historical predecessor and diff remain
shipped. The [evidence guide](data/intake193-source153/README.md) distinguishes
all fresh finite/source checks from delivered universal runtimes. The original
process aggregate intentionally says that semantic audit was pending; the
separate 92-gate review establishes PASS.

## Source 154: five leaves

Follow the [five-leaf guide](intake193-source154-fresh-reproduction.md), with
packet root:

```text
/tmp/intake193-recovered/ZFC_218_Research_2026-10-20/ZFC_218_Research_2026-10-20
```

The portable runner is the exact executed runner and accepts explicit input
and output paths. Five new theory regressions each had a 60-second cap.
Their [actual record](data/intake193-source154-fresh/actual.json) and
[independent semantic audit](data/intake193-source154-fresh/actual-review.json)
retain successful exits, raw streams, input bindings and mathematical scopes.
The optional baseline/source audits were not run.

## Cache-return combination

The own [217 research packet](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k217/research/cache-return/README.md)
provides source/startup reproduction and the completed bounded-fold evidence.
It includes the first failed own assertion, corrected role selection and
independent source review. It is not an accepted new full-runtime certificate
or a 216-state construction. Full ordinary conclusions and unresolved work
are in the [intake reconciliation](intake-193.md).

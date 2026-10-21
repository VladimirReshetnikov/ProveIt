# Source 149: selected fresh reproduction

Eight reviewed direct checks passed on one disposable copy of the original
`K218_Dominated_Rho8_2026-10-20` packet. The exact process commands, timeouts,
input identities and child stdout/stderr are in [actual.json](data/intake191-source149/actual.json).
The [independent actual audit](data/intake191-source149/actual-review.json)
checks the semantic result gates as well as exit status. The [source review](intake191-source149-review.md)
explains the ordinary proof and its inherited calibration.

The archive arrived at `7071e5041ee316d087661b658362feed159901ef`; the
[placement map](data/intake191-placement.json) accounts for its members under
Source 149. Its original report and proof appendices remain recoverable from
that Git object. No delivered manifest or checksum wrapper was executed.

From the repository root, using new temporary paths:

```sh
git show 7071e5041ee316d087661b658362feed159901ef:docs/incoming/K218_Dominated_Rho8_2026-10-20.zip > /tmp/source149-original.zip
python3 -m zipfile -e /tmp/source149-original.zip /tmp/source149-recovered
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake191-source149/replay.py \
  --packet /tmp/source149-recovered/K218_Dominated_Rho8_2026-10-20 \
  --output /tmp/source149-fresh-run
```

The runner copies the packet before executing any of its code, requires a new
output directory, uses Python with assertions enabled, and runs the following
serial leaves. The first seven have a 45-second limit each; the final combined
startup/runtime job has a 240-second limit.

| Job | Checked result |
| --- | --- |
| Shared-term logical forward checker | 3,728 proof nodes; unrestricted rho8 root 3,727 |
| Independent tuple logical forward checker | Same exact schema/root and rule counts |
| Source constructor | Three closed splices; 206-node reference; equivalence to the final 203-node source |
| Independent source/CFG checker | All 186 outside-AX paths and all 6,176 guarded cases |
| Native table reconstruction | Exact 218-state, 436-row table |
| Compact-table audit | Exact state-label bijection |
| Independent complete blank audit | 312,605 steps; exact final tape |
| Startup and universal symbolic runtime | Same startup; all 6,176 arbitrary-natural cases |

No search, ancestor proof, manifest validation, Prover9, Lean or Rocq is run.
The full runtime is an executable symbolic derivation with unary/list induction,
not finite sampling of register values. Its accepted result records 1,616,989
symbolic steps, four exact-table list schemas, all 436 rows and positive duration
constants at least 13. That phase took 162.451 seconds; the final combined process
took 165.614 seconds. The input code/data remained unchanged.

The saved raw child logs are in [logs/](data/intake191-source149/logs/).
The large freshly generated startup and case records are losslessly gzip
compressed in [results/runtime/](data/intake191-source149/results/runtime/).
Their uncompressed bytes exactly reproduce the submitted records. The original
aggregate retains its actual scratch paths, rather than pretending it ran at
these later publication paths. No separate outer-runner stdout file was saved;
the terminal completion was observed, and every child process has its raw logs.

To recheck the published records without executing the submitted checks again:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake191-source149/review_saved.py \
  --evidence SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source149 \
  --packet /tmp/source149-recovered/K218_Dominated_Rho8_2026-10-20 \
  --output /tmp/source149-saved-record-review
```

This own metadata reader supports the saved gzip records and relocates only
historical log paths. Its [focused adapter diff](code/intake191-source149/review-portability.diff)
and the [exact original reviewer](code/intake191-source149/history/review_actual.py)
are retained. It does not create a fresh runtime proof.

For the independent literal source comparison alone:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake191-source149/source_compare.py \
  --repo "$PWD" \
  --packet /tmp/source149-recovered/K218_Dominated_Rho8_2026-10-20 \
  --output /tmp/source149-source-comparison
```

The comparison uses only parsed data and its own tree/CFG reader. Its
[original result](data/intake191-source149/source-comparison.json) and
[path-only adapter](code/intake191-source149/comparison-portability.diff) are retained.
It proves no new physical allocation or state saving.

# Source 151: selected replay

Recover the archive using the [batch guide](intake-191-reproduction.md). Make a
fresh directory `/tmp/source151-fresh` and copy the recovered inner
`zfc-217-research` directory into `/tmp/source151-fresh/packet`. Keep the
pristine recovery untouched. From that scratch `packet` directory run:

```sh
python3 -B code/replay_runtime.py omit-zero --output /tmp/source151-fresh/omit-runtime
python3 -B code/replay_runtime.py dmn --output /tmp/source151-fresh/dmn-runtime
```

Each selected process had a 360-second external cap in the actual run. The
unchanged historical parallel driver is
[history-run.py](code/intake191-source151/history-run.py). Its parent directory
must contain `packet`, so it is executable after copying into a fresh scratch
directory with that layout. It writes individual execution records and raw
stdout/stderr, then `executions.json`. It is not an omnibus verifier.

Copy [history-audit_selected.py](code/intake191-source151/history-audit_selected.py)
to `/tmp/source151-fresh/audit_selected.py`, and run it there with `python3 -B`.
It imports only selected `verify` leaf functions and the dense startup checker;
the manifest loop in `verify.main` is never called. The original fresh audit
took 0.449 seconds. Preserve any failure instead of treating process exit as
the only acceptance condition.

| Check | Omit-zero | DMN |
| --- | ---: | ---: |
| Working states / rows | 218 / 436 | 218 / 436 |
| Guarded runtime cases | 6,142 | 6,167 |
| Symbolic rules | 1,511,359 | 1,516,795 |
| Minimum positive duration | 12 | 12 |
| Complete blank transitions | 312,909 | 123,776 |
| Final state / head | 84 / −5 | 84 / −4 |
| Extra gap | 80 | 23 |
| Candidate / additive counters | 3 / 3 | 2 / 2 |
| Spare ones / complete one cells | 130 / 277 | 72 / 159 |

All other logical registers are zero. Both startup checks compare every cell
of a dense tape against a directly constructed expected frame; neither infers
success only from a dispatcher visit. The complete runtime covers every
literal row on arbitrary natural frame parameters through symbolic induction.

The [actual execution records](data/intake191-source151/executions.json),
[fresh comparison](data/intake191-source151/fresh-review.json), and
[selected audit](data/intake191-source151/selected-audit.json) retain what ran.
The exact case JSON is losslessly compressed in `omit-runtime/cases.json.gz`
and `dmn-runtime/cases.json.gz` under `data/intake191-source151/`.
All regenerated case objects agree with the delivery; runtime metadata differs
only in Python version and elapsed time. The ordinary compiler/enumerator
argument and its limits are in the [source review](intake191-source151-review.md).
No prototype search, abstract reachability replay, manifest suite, ancestor
startup or proof assistant was selected.

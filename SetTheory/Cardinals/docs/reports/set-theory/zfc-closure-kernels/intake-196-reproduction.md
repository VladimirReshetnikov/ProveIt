# Recovering the two research packets

From the repository root, recover both complete original layouts into a new
directory outside the repository:

```sh
uv run --no-project python -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake196.py /tmp/research196-recovered
```

This restores 116 Source157 and 227 Source158 files from `d3d6b8c14e` without
executing supplied code. Placement `943e1685eb` retired both ZIPs. The
[map](data/intake196-placement.json) includes all renamed paths, aliases and
archive-only manuscripts. Several historical discovery drivers require
unshipped masks, frame lists or allocation modules; their delivered READMEs
retain those limitations. The selected leaves below have complete inputs.

For Source157, prepare the narrowly selected plan and run its six leaves:

```sh
uv run --no-project python -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake196-source157/prepare_replay.py --package /tmp/research196-recovered/ZFC_217_Scanner_Source_Research_2026-10-21/ZFC_217_Scanner_Source_Research_2026-10-21 --output /tmp/research157-plan.json
uv run --no-project python -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake196-source157/run_selected.py --plan /tmp/research157-plan.json --output /tmp/research157-fresh
```

The runner copies the packet, removes only the source verifier's manifest
loop using the preserved exact adapter, and retains its original input and
all overwritten copy-side receipts. Mathematical assertions are unchanged.
Each job has a 120-second external cap and assertions enabled. Expected
status is `PASS_ALL_SIX_SELECTED`, with all 45 semantic gates passing.
The six results are the local scanner blocks, startup/wrong-return witness,
two fragment matrices, 79-node equality certificate, local7 source witness
and six complete source recodings. The original run took about 1.03 seconds.

The [actual record](data/intake196-source157/execution/actual.json),
[logs](data/intake196-source157/execution/logs/),
[outputs](data/intake196-source157/execution/output/) and
[55-check artifact audit](data/intake196-source157/review/actual-review.json)
retain exact outcomes. The historical bundle includes its original runner,
plan and an own draft that failed AST parsing before execution. No supplied
job failed. The [detailed guide](data/intake196-source157/source157-reproduction.md)
also retains the original bundle-relative invocation.

For Source158, run the three standalone leaves on another disposable copy:

```sh
uv run --no-project python -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake196-source158/run_selected.py --packet /tmp/research196-recovered/zfc217-research-2026-10-21/zfc217-research --output /tmp/research158-fresh
uv run --no-project python -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake196-source158/review_actual.py --actual /tmp/research158-fresh/actual.json --output /tmp/research158-review.json
```

These have 60-second caps and require the 79-node native-code3 proof, all 62
separate row refinements/3,968 cylinders with a rejected control, and the
104,082-step scanner startup with its precise seven-zero failure and
2,410-step abstract-source reachability witness. The original jobs took
0.243 seconds total. [Actual](data/intake196-source158/fresh/actual.json),
[outputs](data/intake196-source158/fresh/results/) and
[saved-record audit](data/intake196-source158/fresh/actual-review.json) retain
the evidence. No delivered-code adapter was needed.

Each packet's executor also authored its separate saved-record audit; neither
is presented as an independent second-agent peer. The mathematical dossiers
separately justify unbounded source/seed assertions and limit fragment models
to their stated scope. No wrapper, checksum manifest, old full runtime,
ancestor suite, broad search, compiler or proof assistant was executed by
these nine selected jobs. The later K216 row-rebinding research has its own
[portable checker and records](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k216/research/row-rebinding/README.md).

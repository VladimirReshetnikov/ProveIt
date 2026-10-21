# Recovery and selected replay for batch 191

From the repository root, recover the four unchanged arrival archives into a
new directory outside the repository:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake191.py /tmp/intake191-recovered
```

This restores all 936 original members and executes nothing. The tested
[recovery receipt](data/intake191-recovery.json) and
[placement map](data/intake191-placement.json) retain original names and roles.
The four ZIPs are retired in placement `4a1218d878`. Their articles, PDFs,
delivery records and all experiments remain recoverable from `7071e5041e`.

Use Python with assertions enabled, without `-O` or `PYTHONOPTIMIZE`. The
selected jobs below run on copies, because several supplied leaves write
beside their source. Exact historical runners and actual command records
remain preserved; their old absolute scratch paths are historical facts.
No command below invokes a checksum-manifest suite, ancestor wrapper, proof
assistant, or broad search. Do not substitute an omnibus `verify.py` call.

## Source 148: eight selected leaves

The own path-only portable adapter creates a copy and executes the eight
reviewed jobs with 60-second bounds, except the final runtime's 300-second cap:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake191-source148/replay_portable.py /tmp/intake191-recovered/K217_Search_Round_2026-10-20/K217_Search_Round_2026-10-20 /tmp/source148-fresh
```

See the [source-specific guide](intake191-source148-reproduction.md),
[actual result](data/intake191-source148/actual.json), and raw
[logs](data/intake191-source148/logs/). The guide's `replay1/` names refer to
the original execution tree; the published result is `actual.json`. The
portable adapter changes only input/output path selection, with its diff
beside the exact historical runner. Expected aggregate status is
`EIGHT_SELECTED_LEAVES_PASS`. This checks the distinct crossover217 runtime
and its failed blank initialization separately; it does not accept that table.

## Source 149: eight selected leaves

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake191-source149/replay.py --packet /tmp/intake191-recovered/K218_Dominated_Rho8_2026-10-20/K218_Dominated_Rho8_2026-10-20 --output /tmp/source149-fresh
```

The [detailed guide](intake191-source149-reproduction.md) gives each semantic
gate, time bound and independent saved-record audit. Both logical readers,
source/CFG checks, exact table/canonicalization, complete startup and universal
runtime passed. [Actual commands and raw outcomes](data/intake191-source149/actual.json)
and [independent evidence review](data/intake191-source149/actual-review.json)
are distinct from the ordinary mathematical review. Compressed fresh case
files retain exact uncompressed bytes.

## Source 150: five cheap leaves

Copy the recovered `ZFC_217_Investigation_2026-10-20` inner directory to a fresh
scratch directory. In its `formalism/` subdirectory run, each with a 120-second
external process bound:

```sh
python3 -B check_self_vacuity.py
python3 -B check_fixed_b_countermodels.py
python3 -B check_persistent_negation.py
```

From the scratch packet root, with new output locations:

```sh
python3 -B root-search/code/check_preliminary_failure.py --packet-root . --output /tmp/source150-preliminary
python3 -B root-search/code/check_raw_frame.py --packet-root . --output /tmp/source150-frame
```

The same 120-second bound applies. The [original selection plan](data/intake191-source150/replay-plan.json)
also lists `core-quick`; that overlapping leaf was deliberately **not run**.
The [actual five executions](data/intake191-source150/executions.json), stdout,
stderr, generated [formalism evidence](data/intake191-source150/formalism/)
and [diagnostics](data/intake191-source150/outputs/) are preserved. The exact
historical parallel driver is in `code/intake191-source150/history-run.py`.
No source-price or broad machine-search result is claimed freshly replayed.

## Source 151: two runtimes and selected independent audit

Follow the [separate guide](intake191-source151-reproduction.md). The two fresh
full runtime jobs each had a 360-second cap. Their case objects reproduce the
delivery exactly; only elapsed time and Python version differ in the aggregate
runtime metadata. A separate driver checks source edits, four unary-block
schemas, canonicalization, ordered delivered coverage and two **fresh complete
dense-tape blank endpoints**. It does not call `verify.main` or the unchanged
ancestor startup. This separation is preserved in the [fresh review](data/intake191-source151/fresh-review.json)
and [selected audit](data/intake191-source151/selected-audit.json).

All mathematical limitations and retained unexecuted research are recorded in
the [intake](intake-191.md). A successful selected replay is not a Lean/PA
endpoint or a proof that 218 is minimal.

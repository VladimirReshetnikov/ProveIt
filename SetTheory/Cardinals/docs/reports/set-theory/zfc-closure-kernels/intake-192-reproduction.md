# Recovering and replaying K217

From the repository root, choose new paths outside the repository:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake192.py /tmp/k217-recovered
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake192-fresh/run.py --packet /tmp/k217-recovered/K217_Dominated_Continuation_2026-10-20/K217_Dominated_Continuation_2026-10-20 --output /tmp/k217-fresh
```

Recovery restores all 39 members of the arrival at `8a1796545e` and executes
nothing. It includes the exact Source 149 parent archive; that alias is
recorded in the [placement map](data/intake192-placement.json). The incoming
K217 ZIP was retired in `bf087d590f`. Articles and delivery records remain
recoverable in their original paths.

The own selected runner makes a disposable copy, safely extracts its pinned
parent, and runs five direct leaves: reconstruction, independent source/fold
audit, independent complete blank audit, local all-tape fold, and the exact
parent runtime driver against the new table/source. Python assertions must
remain enabled. It uses 60/60/60/90/300-second external process caps and saves
raw stdout/stderr and individual actual outcomes. Expected aggregate status
is `FIVE_SELECTED_LEAVES_PASS`.

The parent proof, logical certificates and full original runtime were already
reviewed/freshly checked for Source 149. This replay does **not** execute
`verify.py`, its checksum-manifest loop, `parent/verify_all.py`, recursive
ancestor verification, broad searches or a proof assistant. No input or
supplied checker is edited. The portable runner's path-only diff and exact
historical runner are retained with the code.

The [actual execution record](data/intake192-fresh/actual.json),
[independent result audit](data/intake192-fresh/actual-review.json),
[raw logs](data/intake192-fresh/logs/) and
[fresh runtime](data/intake192-fresh/runtime/runtime.json) preserve the result.
Large startup and ordered-case JSON files are losslessly compressed; their
uncompressed objects retain the exact fresh output. All 6,176 case objects
match the delivery, with 1,616,558 symbolic rules, all 434 native rows and
minimum positive duration 13. Only elapsed time differs in aggregate runtime
metadata.

The blank audit independently computes all 312,617 transitions with sparse,
dense and canonical-table interpreters. Because its input directory does not
contain `validation/startup.json`, it compares against a directly constructed
complete frame, not a previously saved event list. Its stored-trace count is
zero. The runtime leaf separately generates all 312,617 fresh trace events;
the two complete tape supports agree. Do not relabel this as a fresh replay
of the delivery's stored trace.

The local fold must report 962,479 invariant contexts, 256 nontrivial ones,
maximum old/new block lengths 1/3 and rejection of the corrupt-initial-halt
control. Its finite windows establish an inductive all-initial-tape relation;
they do not replace the separate source, runtime, startup or calibration
arguments. Those are explained in the [intake](intake-192.md) and
[public candidate proof](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k217/proof.md).

The [detailed selected-run guide](intake192-fresh-reproduction.md) gives the
`review_saved.py` commands for fresh or published evidence, with retained
path/gzip adapter diffs. This audits records without rerunning the candidate. No exact-table Lean or internal PA endpoint is claimed.

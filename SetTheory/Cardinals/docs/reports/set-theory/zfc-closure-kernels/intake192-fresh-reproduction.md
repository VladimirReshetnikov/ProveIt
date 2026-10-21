# Five selected fresh checks for K217

The exact run was performed by root after independent ordinary proof and source
reviews. All five selected leaves passed. This packet preserves the unchanged
[actual commands and outcomes](data/intake192-fresh/actual.json),
[raw child logs](data/intake192-fresh/logs/), and root's
[read-only actual-record review](data/intake192-fresh/actual-review.json).
The supplied omnibus wrapper, manifest suite, ancestor verification, logical
certificate and proof assistants were not run. Source149 calibration and its
eight accepted fresh jobs are inherited explicitly.

## Reproduce the selected leaves

Recover the arrival archive from `8a1796545e` using the batch recovery guide.
Set `K217_PACKET` to its inner directory containing `code`, `machine` and
`parent`; this is a path to the recovered directory, not to a ZIP or to its
outer extraction directory. From the repository root, with assertions enabled:

```sh
K217_PACKET=/absolute/path/to/recovered/K217_Dominated_Continuation_2026-10-20
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake192-fresh/run.py --packet "$K217_PACKET" --output /tmp/k217-fresh-replay
```

The output directory must be new. The adapter copies the packet, safely checks
and extracts its exact nested dominated-K218 predecessor, then runs the same
five leaves serially. It changes only input/output path selection from root's
[original runner](code/intake192-fresh/history/run_selected.py); the
[exact diff](code/intake192-fresh/history/run-path-cli.diff) is retained.
No archive code is imported merely to make the plan portable.

| Job | Process cap | Required outcome |
| --- | ---: | --- |
| Reconstruction | 60 s | Three rotations and exact rebuilt source/native/canonical table |
| Independent source/fold audit | 60 s | Full CFG, expected decoder roles and written-marker fold |
| Independent blank audit | 60 s | Complete sparse/dense/canonical startup frame |
| Independent local-fold checker | 90 s | All-tape joint diagrams and rejected negative control |
| Parent runtime driver on new217 source/table | 300 s | Complete positive quantified primitive contracts and startup |

The historical runner checks process outcomes and expected leaf statuses. The
saved-record reviewer below additionally enforces the exact local-fold status,
negative control, complete ordered case census, row coverage and full startup
identities. Use both; process exit alone is not the final acceptance criterion.
No ancestor wrapper is called. The nested parent supplies the already reviewed
symbolic driver and induction helpers, not a replay of its logical certificate.

## Review saved evidence without running a candidate

For a newly reproduced run:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake192-fresh/review_saved.py --records /tmp/k217-fresh-replay --packet "$K217_PACKET" --parent /tmp/k217-fresh-replay/parent/K218_Dominated_Rho8_2026-10-20 --output /tmp/k217-fresh-record-review.json
```

For the published saved evidence, extract only the nested parent (no execution)
and point the reviewer at the maintained records:

```sh
python3 -m zipfile -e "$K217_PACKET/parent/K218_Dominated_Rho8_2026-10-20.zip" /tmp/k217-review-parent
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake192-fresh/review_saved.py --records SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake192-fresh --packet "$K217_PACKET" --parent /tmp/k217-review-parent/K218_Dominated_Rho8_2026-10-20 --output /tmp/k217-published-record-review.json
```

The review output file must be new. The reviewer reads ordinary JSON or a
lossless `.json.gz` fallback. It resolves historical receipt paths relative to
the original run directory recorded in `actual.json`; it does not rewrite those
historical paths. Root's [original reviewer](code/intake192-fresh/history/review_actual.py)
and the [path/CLI/gzip diff](code/intake192-fresh/history/review-path-cli-gzip.diff)
are retained. All original assertions are unchanged. The adapter's fresh
[read-only validation](data/intake192-fresh/portable-saved-review.json) reproduces
root's original review byte for byte; no candidate was rerun to validate it.

## Exact fresh results and scope

The final runtime covers 6,176 ordered guarded cases, 1,616,558 symbolic rules,
all 434 transition rows, and minimum positive duration constant 13. Its internal
runtime timing is 158.7638279525563 seconds; the entire runtime-driver process,
including startup and output work, took 161.70451156329364 seconds. The represented
registers, gaps and finite spare lists remain arbitrary natural parameters.
The finite case-derivation search limit does not bound those represented values.

The complete startup has 312,617 newly generated trace events, dispatcher84,
head−5, gap80, registers `[3,0,0,0,3,0,0,0,0]`, 130 one-valued spares and277
one cells. The independent blank audit computes the full sparse/dense/canonical
prefix and complete support. Its count of compared **stored** trace rows is0:
there was no stored full-trace input at its default path. This is distinct from
the new complete trace emitted by the runtime driver. Root's record review
compares the independent complete support with that fresh runtime endpoint.

The joint-fold checker covers962,479 inductive window contexts, maximum blocks
one old step versus three new steps, and rejects the corrupt-initial-halt
negative control. Its all-tape claim is from initial state0, with marker entry
invariants, not from arbitrary configurations already inside the merged pair.

The large [case receipts](data/intake192-fresh/runtime/runtime_cases.json.gz) and
[fresh startup trace](data/intake192-fresh/runtime/startup.json.gz) are compressed
losslessly. All other fresh receipts, rebuilt outputs and ten child stdout/stderr
files retain their exact bytes. The raw runtime cases equal the delivery;
only elapsed time differs in runtime metadata. The original runners did not
save a separate outer-shell transcript; none is reconstructed here.

The [first ordinary proof/code review](data/intake192-fresh/source-review.json),
[full dossier](data/intake192-fresh/source-review.md),
[code-closure comparison](data/intake192-fresh/code-closure.json), and
[second independent source review](data/intake192-fresh/second-source-review.json)
retain their pre-execution checkpoints unchanged. Root owns the subsequent
actual execution/review. These evidence layers support an ordinary argument
formalizable in ZFC using inherited calibration. They are not a new exact-table
Lean/Rocq or internal PA endpoint, unconditional nonhalting, minimality or216-state
result. The independent candidate prose check is
[separate](data/intake192-fresh/candidate-prose-review.json).

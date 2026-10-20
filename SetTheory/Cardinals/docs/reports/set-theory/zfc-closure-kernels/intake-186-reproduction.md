# Recovering and replaying the 219-state construction

The [placement map](data/intake186-placement.json) accounts for every original
member of Source 140. Restore the complete original package from its committed
arrival, then replay the selected checks on another disposable copy:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake186.py /tmp/zfc186-packets
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/replay-intake186.py --packets /tmp/zfc186-packets --output /tmp/zfc186-replay
```

Run from the repository root with Python 3.10 or later, standard library and
assertions enabled. Both output directories must be new and outside the
repository. Recovery uses Git arrival `26d5de6d21fa354d50e0b84fe851c289925b8d72`,
checks ZIP paths, and executes nothing. The intake freshly recovered all 110
members. Replay copies the restored K219 packet, unpacks its exact included
K220/K221 predecessors, and writes all new results under the requested output.
The complete original parent chain remains available without network access.

The seven selected jobs are source replacement, literal machine construction,
canonicalization/sparse-dense startup, complete final symbolic runtime,
independent runtime audit, independent state108-role/startup audit, and finite
countermodel algebra. Each has a 120-second timeout except the complete
runtime, which has 1,200 seconds. Failures retain logs and stop the sequence.
The wrapper checks rebuilt source and native/canonical bytes against the
release. Do not run Python with `-O` or set `PYTHONOPTIMIZE`.

During intake, the five core jobs ran through a scratch orchestration script;
the two supplements ran separately. The public wrapper consolidates those
same commands. Their original absolute scratch paths remain in the records
as execution provenance, not required public paths:

- [Five core jobs](data/intake186-fresh-replay/actual.json),
  [runtime](data/intake186-fresh-replay/runtime/runtime.json),
  [independent audit](data/intake186-fresh-replay/runtime_audit.json).
- [State108/startup job](data/intake186-fresh-supplemental/actual.json) and
  [result](data/intake186-fresh-supplemental/literal-audit.json).
- [Finite algebra job](data/intake186-fresh-theory-replay/actual.json) and
  [result](data/intake186-fresh-theory-replay/finite-algebra.json).

All seven passed; the full runtime took about 143 seconds. This scope excludes
supplied manifest wrappers, recursive ancestor replay, proof-assistant builds,
exhaustive search and a kernel proof of the equality contract or HC model.
Those two unbounded arguments were independently reviewed as written mathematics.
The finite algebra checker alone does not establish the HC result.

## Reproducing the intake's additional row157 variant

The separate [publication](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k219/README.md)
contains the exact canonical/native baseline and the intake's same-size variant.
After the seven checks above, run from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/candidate-k219/code/stack_row157.py \
  --baseline /tmp/zfc186-replay/construction/candidate.tm \
  --baseline-receipt /tmp/zfc186-replay/canonical/canonicalization.json \
  --checker Computability/BusyBeaver/Research/ZFC/candidate-k219/variant-row157/check_joint_fold.py \
  --output /tmp/zfc186-row157
```

Use a new output directory. This constructs just the single specified row
change, runs the unchanged earlier independent window checker with a 120-second
cap, canonicalizes the result, and checks complete sparse/dense startup. The
result is another 219-state table, not a state-count reduction. It transports
the baseline's ordinary calibration through the all-tape equivalence from
state 0; it does not rerun its primitive runtime. The earlier author preflight
failure is retained in `variant-row157/history/`; the published reconstruction
script contains the corrected helper directions.

## Delivered-layout caveats

Run delivered scripts from recovered original layouts, not their flattened
`140-k219-` archival names. Main report build scripts require archive-only TeX
inputs. The countermodel Markdown's command uses the author's historical
`research_calculus/` path; the actual shipped checker is
`research/theory/restricted_rho8_strong_countermodel.py`. It writes its finite
result beside itself, so run it only on a disposable copy, with assertions on.

The supplied research runner prepares its own parent dependencies and retains
bounded-search receipts. No provisional failed-machine tables are promised
by that research directory. The codec findings' historical
`research_encoding/clean_eq_proof.tex` names the proof now delivered at
`report/sections/equality.tex`; old generated-search references correspond to
`research/experiments/receipts/` summaries. Raw compiler counts and finite interfaces are
not candidate correctness theorems. Historical report build logs and receipt
paths remain unedited; the intake's records are separate. Checksum-manifest
validation and line-ending normalization are not intake work.

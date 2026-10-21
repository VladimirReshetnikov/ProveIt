# Recovering and replaying K216

From the repository root, choose new directories outside the repository:

```sh
uv run --no-project python -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake195.py /tmp/k216-recovered
uv run --no-project python -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake195-fresh/run.py --packet /tmp/k216-recovered/K216_Partial_Selector_2026-10-20/K216_Partial_Selector_2026-10-20 --output /tmp/k216-fresh
uv run --no-project python -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake195-fresh/review_saved.py --records /tmp/k216-fresh --packet /tmp/k216-recovered/K216_Partial_Selector_2026-10-20/K216_Partial_Selector_2026-10-20 --output /tmp/k216-review.json
```

Recovery restores all 41 original members from `6ec69081ca`, including the
article, proof sections, PDF, delivery README and exact Source 152 parent
archive. It executes no supplied code. Placement `58615b1aa1` retired the
incoming ZIP. The [placement map](data/intake195-placement.json) gives every
renamed destination and exact alias, with original introduction commits.

The selected runner makes a new disposable copy and safely extracts the
parent as data. It runs five direct leaves with assertions enabled:
reconstruction, source equivalence, marker/blank audit, all-tape local fold,
and complete symbolic runtime. It saves raw stdout/stderr and individual
outcomes under the selected output. Process caps are 60, 60, 60, 90 and 360
seconds. Expected terminal status is `FIVE_SELECTED_LEAVES_PASS`; the runtime
driver's exit code alone is insufficient because its unproved outcome also
returns zero. The runner checks its JSON status, case count and failures.

The final record auditor executes no machine. It checks the saved artifacts,
ordered cases, durations, row coverage, complete startup, source correspondence
and control result. It accepts plain or losslessly compressed large JSON
files. The published [actual record](data/intake195-fresh/actual.json),
[output review](data/intake195-fresh/actual-review.json),
[logs](data/intake195-fresh/logs/),
[runtime](data/intake195-fresh/runtime/runtime.json) and
[source proof](data/intake195-fresh/source/verification.json) preserve the
fresh outcomes. Historical absolute paths in these records describe the
actual run; use the portable commands above for new execution.

Expected runtime totals are 6,176 cases, 1,709,992 symbolic rules, all 432
rows and minimum positive affine duration constant 13. The fresh complete
startup has 313,133 trace events, dispatcher 84, head −5, gap 80, registers
`[3,0,0,0,3,0,0,0,0]`, 130 one-valued spares and 277 one cells with zero
exterior. Unlike batch 192's particular invocation, the separate blank audit
does compare every native event against a delivered stored trace, while
independently simulating both the native and canonical tables.

The local proof reports 27,527 inductive contexts, 48 nontrivial ones,
maximum old/new block lengths 1/3, and rejection of a corrupt initial halt.
The source proof preserves 6,175 guarded edges and the one terminal case.
These obligations are distinct from the inherited logical calibration.

The supplied `verify.py` wrapper begins with checksum-manifest validation and
also invokes parent verification. It is not used by this replay. No checksum
manifest, recursive ancestor suite, old logical certificate, broad search or
proof assistant is rerun. Previously accepted Source 149/152 calibration is
inherited with its stated scope. The exact216 Lean/internal PA endpoint
remains open.

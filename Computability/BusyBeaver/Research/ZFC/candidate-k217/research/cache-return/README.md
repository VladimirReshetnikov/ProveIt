# Cache-return composition on the 217-state source

Source 154's shorter successful-MP convention combines with the accepted
217-state source, but has not yet saved a physical state. This is research
with a complete source/decoder check and unchanged startup, **without a fresh
full modified runtime**. The accepted parent remains the primary contender.

Replace the closed 26-leaf success suffix at `111111` by
`(CD4,(CI5,CC2))`. This moves the conclusion into the cache instead of pushing
a dummy zero and copying the conclusion into the current-formula register.
The only physical change is `164/1: 1 R 98 -> 1 R 130`.

| Property | Result |
|---|---|
| Working states / rows | 217 / 434 |
| Primitive leaves / distinct subtrees | 4,728 / 203 |
| Depth / maximum zero run | 45 / 6 |
| Guarded primitive cases | 6,146 |
| Expected internal decoder bindings | 4,727 |
| Exact leaf-action bindings | 4,728 |
| Retained CFG edges checked by two readers | 6,141 |
| Complete unchanged parent startup | 312,617 transitions |
| Native table SHA-256 | `0b2ec7ca3440d3afac79d5d3b05dd18f1b2db0db185e85e8894a666cae046eeb` |
| Source SHA-256 | `a886e210643d51d48fd8f29f78b291da7643869c715436dd99686ec631504e7b` |

The [ordinary transfer argument](ordinary-transfer.md) uses the exact dominated
common-input compiler. Successful MP returns `(0,W,0,G)`; `DROP,NIP` restores
`(G,W,0,0)`, or halts correctly for G=1. Existing discard, row, bundle, GEN and
cofinal START constructions remain valid. This argument assumes the changed
command's full arithmetic behavior; exact decoder entry bindings and finite
startup do not discharge a new whole binary runtime.

[The composition receipt](run2/composition.json), [source](run2/sites.json),
[table](run2/candidate.native.tm), [raw stdout](run2.stdout) and
[independent focused peer](peer/review.json) preserve the precise checked
scope. The peer read the full constructor and relevant helper definitions and
used a separate literal parser; it did not rerun the complete startup.

The first own constructor incorrectly assumed that state 130 had only one
source role. It has two. The corrected version selects its exact existing
three-leaf transfer at `111010010011101111`, with the same predecessor marker,
and checks every required prefix and leaf binding. [The initial constructor](compose-v1.py)
and [failed assertion](run1.stderr) remain preserved. No candidate proof
condition was weakened. The peer's own inert-reader syntax correction is
also retained in its history.

## Completed bounded search

The new table was searched over all 46,872 ordered keep/drop pairs, including
432 pairs involving the initial state. It covered 645,408 distinct candidates:
186,428 inherited-action specifications and 458,980 one-common-action
specifications. Every candidate failed the radius-7, fuel-97 local proof
filter; none reached the independent accepting checker. It completed in
36.412 seconds under a 110-second soft and 120-second external cap.

[Result](folds/run1/result.json), [execution](folds/execution.json),
[raw output](folds/run1.stdout), [compressed rejection records](folds/run1/rejections.jsonl.gz)
and the separate [whole-stream metadata audit](folds/metadata-audit.json)
retain the complete census and exact scope. The audit checks enumeration,
unique specifications and record membership, not the semantics of failed
joins. These finite proof-search failures are not counterexamples to arbitrary
folds and are not lower bounds on machine size.

## Reproduction and provenance

From the repository root, with a new scratch output directory:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/candidate-k217/research/cache-return/compose_portable.py \
  --repo "$PWD" --output /tmp/k217-cache-reproduced
```

The source-reviewed portable adapter changes only explicit repository/output
selection and adds an assertion-enabled check. It was not used for the original
run; [the exact original](compose.py) and [path diff](compose-paths.diff) are
preserved. It reads the accepted parent's fresh compressed startup trace and
checks every transition against both tables. All expected source/runtime
inputs remain in the maintained repository. It does not execute a manifest,
ancestor wrapper, broad search or proof assistant.

The search scripts and original driver remain under `folds/`. Their historical
absolute paths in receipts are provenance. A new search must use a fresh output
path and the exact supplied seed, with the documented wall caps; the completed
negative family need not be repeated. The saved-record audit likewise retains
its historical input paths.

The cache convention is credited to Source 154; the parent construction is
Source 152 and its dominated-calculus calibration is Source 149. Their original
notices and licenses remain in the parent publication and retained source
reports. Root authored this composition and bounded search; `drop_contract`
reviewed the source and literal bindings; `review_upstream_reflection` reviewed
the ordinary compiler transfer. See [batch 193](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-193.md).

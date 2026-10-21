# Omit-zero composition and bounded searches below217

The accepted Source152 dominated217 table combines with Source151's proved
dummy-zero omission at the source and startup level. It remains217 states.
One bounded all-state fold search on each of the two exact tables found no
survivor. No216-state machine or state lower bound is claimed.

## Exact composition

The only changed physical row is`164/1: 1 R98 → 1 R114`. The closed19-leaf
PUSH at source path`1111110` is removed, and its closed7-leaf COPY sibling
is promoted from`1111111` to`111111`. This is the successful-MP semantic
change from Source151, with the repair to its proof compiler transferred to
Source149's literal AX/reset equations. Source152 preserves those equations.

The [ordinary transfer](omit-zero/ordinary-transfer.md) proves the strong
command compiler contract by deleting one final NIP in the MP cleanup. It
keeps all dominated-rho8 parameter restrictions, bundle gates, native code0
behavior, and cofinal enumeration. The
[independent source and proof peer](peers/omit-zero-review.json) found no defect
and discloses its author's prior Source149 composition work.

The executed [composition checks](omit-zero/run1/composition.json) establish:

- all retained instruction occurrences and both complete redirected source CFGs;
- the expected state at all4731 internal source prefixes and every retained
  leaf's literal action;
- the exact312617-transition blank-start trace, reconstructed from the blank
  tape and unchanged at every action, including its complete endpoint;
- 217 working states,434 rows,203 distinct source DAG nodes,4732 instruction
  occurrences and6151 guarded cases.

The changed row does not occur in that startup trace. All167 physical decoder
states remain represented, including26 remaining source roles for98. The
shorter source therefore supplies no immediately dead decoder state.

The parent has fresh full primitive runtime evidence. A full primitive runtime
replay for the shortened source was **not** performed. This packet records
the narrower source/decoder/startup composition, not a newly accepted binary
endpoint or proof-assistant theorem.

## Two actual bounded searches

| Exact seed | Ordered pairs | Candidate row specifications | Elapsed | Survivors |
|---|---:|---:|---:|---:|
| Canonical submitted217 |46872|647136|36.594 s|0|
| Submitted217 with omit-zero |46872|645408|36.678 s|0|

Each search includes every ordered pair of distinct working states, including
the initial state. It tries inherited action choices and, when one mapped
branch agrees, every write/move/remaining-target choice for the other branch.
The pinned all-initial-tape local filter uses radius7 and fuel97. The wall
limits remain110 seconds internally and120 seconds externally. Every candidate
was rejected by the bounded filter, so the separate unchanged acceptance
checker was never invoked.

The [author metadata review](folds/review.json) binds both exact results and all
inputs. A separate metadata reader independently enumerated the family and
read every compressed rejection record: sequential IDs, exact family
membership, unique row pairs, all initial-state orientations, and totals.
This checks record integrity and scope; it does not turn a bounded failed
proof search into a counterexample or lower bound. The two runs tested
1292544 specifications in total, once per distinct seed.

Original drivers, narrow metadata-only diffs, raw stdout/stderr, seeds,
complete compressed rejection streams, result records, and the metadata audit
are retained. Author scripts and captured records retain their actual original
absolute paths. Non-evidence interpreter bytecode caches created by a later
metadata read are not published; their historical descriptors remain in the
composition author's original inventory.

## Reproduction

From a fresh disposable copy of this directory, use new output directories:

```
python3 -B omit-zero/compose.py --output /tmp/k217-omit-replay-NEW
timeout 120s python3 -B folds/search.py \
  --seed folds/seed217.native.tm --output /tmp/k217-fold-replay-NEW
timeout 120s python3 -B folds/search_omit.py \
  --seed folds/seed217-omit.native.tm --output /tmp/k217-omit-fold-replay-NEW
```

The composition reads its pinned input copies and frozen compressed startup
trace. It does not invoke an upstream wrapper or repeat the full runtime.
The search drivers import only their pinned local filter and checker copies.
The copied historical metadata audit targets the actual saved run paths; it
is evidence of the original audit, not a path-independent new replay driver.

The successful independent reconstruction of the submitted217 table is
documented separately in [independent-helper-reconstruction](../independent-helper-reconstruction/README.md).
Its saving is the same one used by the submission and cannot be added again.

# Sequential fresh runtime checks

The frozen `check_runtime.py` runs exactly one unit and focused audit. It is not a source emitter or a multi-compiler coordinator. Root owns each invocation. Its manifest pins all eight source/audit identities, probe/caller counts, exact import closures, fixed actual evidence anchors and allowed dependency names. No future object hashes are invented or selected in the manifest.

| Unit | Projects | Probes / callers | Required `--parent` values |
|---|---:|---:|---|
| pulse | 5 | 3 / 4 | none; actual KernelRows is fixed |
| mark | 7 | 10 / 6 | none; actual TableRotation244 is fixed |
| boxes | 9 | 14 / 19 | pulse |
| symbolic | 13 | 15 / 15 | boxes, mark; actual FastTableRotation244 is fixed |
| site | 18 | 12 / 13 | symbolic |
| frame | 22 | 14 / 15 | site |
| instruction | 23 | 7 / 7 | frame |
| runtime | 27 | 11 / 12 | instruction |

Each parent argument consists of three separate values: `--parent UNIT RECORD SHA256`. Only the exact named predecessor set is accepted. A parent must be a successful actual source/audit record for the expected module, source bytes, audit bytes and census. The guard checks zero warnings, standard axiom reports, unchanged default limits, all current before/after inputs, original/snapshot bytes, raw source/audit logs, fresh-source capture before audit and its first-provider identity. Its successful parent object and reused providers then enter an independently recomputed import DFS. No failed, merely prepared, wrong-source or guessed future module can enter the cache.

The fixed generic anchor is the checked RuntimeInstanceRouting245 record. Only unchanged generic modules needed by the new import DFS can be selected from it; old Routing245 machine-specific objects are excluded. That record's legacy warning dictionary, sibling log locations and budget fields are handled explicitly. The current KernelRows/TableRotation/FastTable records and all newly produced runtime records use the modern schema. Every immediate parent's current input set is rehashed, but historical ancestor proofs are not re-executed.

The source/audit process runner is byte-identical to the reviewed KernelRows runner. Each pair shares120seconds with `-j1 -M4096`, no global proof-limit overrides, no version query/download/build, a fresh target object and pre-audit capture, and final input/provider/object checks. Init/Omega are selected exactly as required by the import closure. The complete run is serial.

Initial root commands:

```sh
python3 -B /tmp/zfc-rotation244-runtime-ports-v1/control/check_runtime.py --unit pulse --prepare-only --output /tmp/zfc-rotation244-runtime-ports-v1/pulse/prepared1
python3 -B /tmp/zfc-rotation244-runtime-ports-v1/control/check_runtime.py --unit pulse --output /tmp/zfc-rotation244-runtime-ports-v1/pulse/run1
```

For each later unit, root should compute and freeze the just-completed predecessor record's digest, supply its explicit record and digest, prepare in a fresh output directory, then run in a different fresh directory. The same frozen guard and manifest serve all eight units. Successful independent predecessors can be reused directly; no repeat compilation is needed. Root's outer launcher should preserve stdout/stderr, command, exit status and selected record hashes even for a preflight rejection before the guard creates its output directory. A failed proof attempt is retained; any source or guard repair requires a separately preserved manifest/guard successor and a new attempt directory.

This family proves the reusable runtime only. Exact rotated-tree identity, all8390 site guards, complete bootstrap-frame identification, and the final Rotation244/Combined243 calibration are separate checked units. The full bootstrap has now passed through Chunk010; its fresh frame adapter uses value-one spares and actual padding9/0, while its runtime dependency is still pending.

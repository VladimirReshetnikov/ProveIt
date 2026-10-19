# Direct Rotation240 runtime guard sequence

The frozen `check_runtime.py` is source-only and uninvoked by its author. Root owns preparation and all source/audit execution. It pins `runtime-manifest.json`, the actual seven-source generation, Opening's two-source inventory, and the selected actual Table240/Fast240/generic Runtime245 records. No future object is assumed.

Run Opening's independent KernelRows guard first. After its actual PASS, use the common guard with the exact Kernel record and SHA, for example:

```sh
python3 /tmp/zfc-rotation240-runtime-control/check_runtime.py --unit pulse --parent kernel KERNEL_ACTUAL_RECORD KERNEL_ACTUAL_SHA --output FRESH_PULSE_PREPARED --prepare-only
python3 /tmp/zfc-rotation240-runtime-control/check_runtime.py --unit pulse --parent kernel KERNEL_ACTUAL_RECORD KERNEL_ACTUAL_SHA --output FRESH_PULSE_ACTUAL
```

Replace the uppercase placeholders with existing actual evidence and fresh external directories. Subsequent unit invocations use the same syntax and precisely these parent arguments:

| Unit | Explicit actual parents | Projects | Probes / typed clients |
|---|---|---:|---:|
| Pulse | kernel | 5 | 3 / 4 |
| Mark | none | 7 | 10 / 6 |
| Boxes | pulse | 9 | 14 / 19 |
| Symbolic | boxes, mark | 13 | 15 / 15 |
| Site | symbolic | 18 | 12 / 13 |
| Frame | site | 22 | 14 / 15 |
| Instruction | frame | 23 | 7 / 7 |
| Runtime | instruction | 27 | 11 / 12 |

Each parent uses a separate `--parent UNIT RECORD SHA256` argument. Mark's Table240 and generic dependencies are already pinned. The manifest's Kernel descriptor exists only for checking Pulse's actual parent; this common guard cannot compile Kernel. The eight common-guard units have 86 probes / 91 clients; including the separate Kernel gives 106 / 94.

Every invocation has its own shared 120-second source-and-audit bound, `-j1 -M4096`, default proof limits, exact selected provider closure, and fresh source object captured before audit. The root serial driver should save preparation, invoke only one source/audit pair at a time, stop on any non-PASS or warnings, retain every failure and raw stream, and pass a completed actual record onward only after checking it. Retry only in a fresh directory under a versioned successor when needed. The guard rejects missing/extra parents, changed source/audit/manifest pins, non-PASS predecessors, wrong closures, and changed provider objects.

The fixed generic Runtime245 record retains its observed legacy schema and cache provenance; its machine-specific runtime objects are filtered out by the exact new import closure. Its actual captures are checked; no ancestor recompilation or broader cache refresh is claimed.

These units provide fresh machine-specific runtime contracts. Tree240, all 8,386 site guards, fresh blank bootstrap/frame, and the final binary consistency endpoint remain separate obligations.

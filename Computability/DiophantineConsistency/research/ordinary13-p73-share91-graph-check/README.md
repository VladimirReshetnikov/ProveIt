# Guarded P73 91-operation graph client

This packet prepares an **unrun three-stage Lean guard** for the uncompiled
[P73 shared-graph draft](../ordinary13-p73-share91-lean-draft/README.md). It is
not a model bridge, iPRA endpoint, JSON/PDF semantics theorem, complete
package/dynamic-ancestry audit, or proof that the draft compiles. No Lean run
or build tree is recorded in this packet.

The exact stage order is `Compact44.FreeJ13`, `Compact44.P73Graph`, and the
draft `P73Shared91`. The proposed build uses a fresh isolated output root,
followed by the single retained P72 provider, guarded package overlay and
Lean toolchain; it does not add separate base or FAILED-parent roots. P72's
base links are used in place and no inherited object is copied, changed or
deleted. The guard pins the three sources, their imports and 27 explicit
axiom-report names, the two P72 frontier object routes, Mathlib and Init
routes, the read-only collision survey and independent source/route reviews.
It reruns that collision survey before and after a proposed build.

Actual `lean --deps` output must match the declared direct module names and
the first matching path in the four ordered roots. P72 frontier hashes and
realpaths must match their pinned routes; later stages must use objects just
produced by this run. Each stage records source, dependency, direct-companion,
object and output-companion hashes, both child logs and numeric exits. It
checks the exact stage-specific axiom report names once each, allows only
`propext`, `Classical.choice` and `Quot.sound`, and rejects error diagnostics
and `sorryAx`; warnings remain visible in the logs. Postflight rechecks sources, output/companion hashes, direct
guards, logs, runner identity and the pinned provider survey. Existing output
paths are refused; failed output is retained.

## Resource rules and no-Lean controls

The runner preserves the established 5,100,000,000-byte sampled disk stop,
4-GiB sampled child-RSS cap, 10-GiB host-memory floor, `lean -M3600 -j1
-DElab.async=false`, 180 seconds per child and a six-hour overall stop
trigger. A watchdog starts before the initial guarded preflight and also
checks during hashing. The read-only survey subprocess has a 120-second
timeout and Git queries have 30-second timeouts. Sampling can miss transient
spikes, escaped descendants or filesystem changes between observations.
After a stop, forced log hashing, failure-receipt writing and cleanup may
finish after the nominal wall-time trigger. No preexisting files are removed.

The following commands do **not** launch Lean or create a build tree:

```
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary13-p73-share91-graph-check/controls.py
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary13-p73-share91-graph-check/run.py --inspect
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary13-p73-share91-graph-check/run.py --preflight
```

`controls.py` exercises resource and axiom-report boundaries, duplicate
reports, bad pins, preexisting output, watchdog ordering, Git timeout,
initial/child-stop receipts and a synthetic monitored disk stop. It creates
and removes only its own small temporary control directory and child process.
`--inspect` performs the read-only source/route survey even below the disk
floor and reports the resource refusal; `--preflight` starts its watchdog
and refuses at or below that floor. The frozen
[controls observation](controls-observation.json) records successful no-Lean
controls and inspection, and a numeric preflight refusal on `disk_floor`.
It also confirms the proposed output path was absent at that observation.
Disk is not reserved and all resource observations can change.

`--run` is an explicit separate mode. Do not use it until adequate resources,
independent guard prelaunch review, and exclusive shared Lean-slot allocation
are in place. The source-level `simp` strategy and its default heartbeat
budget remain untested. Even a successful graph guard would establish only
the reported graph-evaluation client with inherited provider limitations;
the model and iPRA endpoint clients are separate work.

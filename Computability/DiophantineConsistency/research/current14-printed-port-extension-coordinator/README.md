# Draft outer-exit coordinator for the 61-module extension

This packet has **not launched the extension**. The reviewed
[extension driver](../current14-printed-port-extension-driver/README.md)
records an internal build state but does not independently retain its own
operating-system process exit. The proposed [`coordinator.py`](coordinator.py)
is a separate wrapper intended to capture that actual child exit and audit
the terminal state before writing PASS. Its default `--check` is read-only;
the real current RUNNING base is refused before any output is created.

**Do not launch this v1 coordinator.** Independent review found that the
pinned extension driver's `run_module` may exit on a monitor exception while
its separately sessioned Lean child remains alive. Waiting for the extension
driver's process exit in this coordinator does not by itself reap that Lean
child. See the [independent review](../../reviews/current14-printed-port-coordinator-independent/README.md).
The v1 source and receipts are retained as historical evidence; a revised,
independently reviewed child-cleanup design is required before launch.

After the base succeeds, the coordinator's preflight calls the pinned
extension driver's full source/base/provider gate, verifies the reviewed
driver and guard hashes, requires at least 10 GiB sampled `MemAvailable`,
at least 4 GB free disk and an idle Lean slot. Only explicit `--run` would
create the exclusive coordinator directory and launch the extension driver.
It records the child PID, exact command, full outer log, sampled progress,
free disk and memory, and the **actual child process return code**. A zero
exit is necessary but not sufficient for PASS.

The separate [`verify.py`](verify.py) checks 61 ordered successful rows,
current and staged source hashes, regular output objects and companion
guards, logs and forbidden proof placeholders, exact recorded direct-import
names/routes and hashes, the extension's authenticated base-overlay guards,
external guards, complete overlay file inventory and namespace-shadow
absences. The coordinator reruns the
base/provider preflight and compares its context before and after this
terminal check, then pins the terminal state and its own scripts. A later
client must still authenticate this terminal receipt and its actual outer
coordinator exit.

If monitoring itself fails while the child is live, the wrapper records
`MONITOR_FAILURE_CHILD_LIVE` if possible and waits for that child's actual
exit before failing closed. It does not kill only the coordinator process
group: the extension driver starts Lean modules in separate sessions, so
such a kill could leave an orphan. While running, memory and disk are
**sampled for observation, not automatically stopped by this coordinator**;
the child driver has its own `-M8000` per-module limit, wall bound and sampled
4 GB disk stop. This is not a hard RSS reservation or an automatic low-memory
stop; operators must assess resource availability, and no unrelated process
should be killed. There is no additional coordinator-wide wall timeout.

The [synthetic controls](controls-observation.json) exited 0 without Lean:
a 61-row terminal fixture passed, while nonzero child exit, missing row,
changed source/object, unexpected companion/import, foreign overlay file,
external namespace shadow, forged pin and optimized Python were rejected.
A fake live child confirmed monitor failure waits for
its exit; the real current base was also refused. Earlier control observations
are retained. These controls do not exercise an actual successful base,
real `lean --deps`, full provider ancestry or an actual extension launch.
The coordinator and its terminal verifier need independent source review
before use; a valid run can still fail due to resource or import-resolution
behavior. Package-transitive, dynamic-loading and between-sample ancestry
remain outside scope.

After a real base terminal PASS and review, the preflight command is:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/current14-printed-port-extension-coordinator/coordinator.py --check
```

It refuses existing coordinator or extension output paths. A running process
must be polled by its actual PID/state; do not launch another copy solely
because an observation times out.

SHA-256: `coordinator.py`
`f898dad6a47934e698249d25545964b7b4dd657a3f4275f0a45c49a1cdce480b`;
`verify.py` `005b0f48f6cb83a3d62c4aa5e5cf5ee3d7cd651e674916f114832b68071061ac`;
`controls.py` `10bba53b815076880c50b3f73172f222906f826e67d541f569393cf826a4d93d`;
`controls-observation.json` `788234816498e3e07dda3a121b2869cafe5ac5ea2781f9eb153df7937e96762c`.

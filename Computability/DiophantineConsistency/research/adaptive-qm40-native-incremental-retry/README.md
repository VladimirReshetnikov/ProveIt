# Focused QM40 native retry

The [previous bounded attempt](../../reviews/adaptive-qm40-native-bounded-replay/README.md)
compiled six author-side model modules, then its `IPRAQM40Native` child hit
the 180-second timeout without an observed native object. It did not attempt
the peer side. The reason for the timeout was not established.

`replay.py` prepares an incremental **single-author** retry of
`IPRAQM40Native` followed by `IPRAQM40NativeChecks`, using the six observed
objects in `/tmp/ipra-qm40-native-author-8thsscoi/lib`. It creates a fresh
direct `/tmp` output root, makes a symlink overlay of the seed, freezes both
Lean sources there, and writes new objects only under that fresh root. The
overlay is necessary because Lean's project module directory selection can
shadow the later seed even when a particular object is absent. The
[first incremental attempt](../../reviews/adaptive-qm40-incremental-shadow-failure/README.md)
hit exactly this issue and exited before elaboration. The historical seed and
package remain read-only inputs. Each compiler child has a 600-second timeout, `-M3000`,
`-j1` and asynchronous elaboration disabled. The checks client requires
three axiom reports and rejects warnings, errors and `sorryAx`. A failed
child is retained as a failure with its available logs and step records; no
successful terminal result follows merely from reaching preflight.

Before and after children, the script checks candidate and source snapshots,
all six previous author outputs and their companion slots, and the direct
dependencies selected by `lean --deps`. It records and checks each direct
candidate's absence or presence, raw symlink text, final resolved target and
hash in each search root. It refuses occupied output slots and never
overwrites an existing output directory. These point-in-time checks do not
authenticate every transitive dependency, intermediate symlink, dynamic load,
or provider state between checks; the earlier model and package ancestry
limitations remain. This is not a matched replay or an independent source
closure.

The corrected no-Lean overlay preflight exited 0 with
`READY_INCREMENTAL_QM40_NO_LEAN` and recorded
[preflight-overlay.json](preflight-overlay.json). Its script SHA-256 is
`e6915734d1d0467dc776061d5eb8ce651538c7bca64e2bc763af7ab6f547a2c6`.
The earlier [preflight.json](preflight.json) belongs to the initial driver
with SHA-256 `31896a24ac4a114d18b344e010c7c28f13ac6a5d41f4f902fde204f101513958`;
that preflight did not detect the subsequent shadowing failure.
The no-Lean controls exited 0 and detected a new companion file, a changed
symlink target with identical bytes, and a changed target payload. Attempts
to reuse the preflight directory, use the seed directory as output, or run
with optimized Python each exited 1 as intended. These controls do not
exercise the Lean or timeout paths. No Lean compilation is claimed here.

With the shared Lean slot reserved, invoke the retry with a fresh output path:

```
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-qm40-native-incremental-retry/replay.py --output /tmp/ipra-qm40-incremental-author-NEW
```

The command includes the native checks module. A passing run would still
prove only the recorded author-side native result on the inherited model
provider, not a paired replay, authenticated complete closure, binding to a
PDF, or the smaller compact44 endpoint.

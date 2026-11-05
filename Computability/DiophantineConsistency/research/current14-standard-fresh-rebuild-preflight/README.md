# Fresh current14 standard-endpoint rebuild preflight

On 2026-11-04, the existing `fresh-project-closure/prepare.py` froze the
declared project import closure of `IPRAStandardCurrentEndpointChecks` from
workspace HEAD `1c2fd36340a300385e29b4492be0c03f1445d9f3`. It captured 1,000
project modules and 106 direct external module names. A source audit exited 0
and found all 1,000 sources tracked, with no differences from HEAD. Its
[snapshot manifest](snapshot-manifest.json) and [audit](source-audit.json)
are preserved here; the source copy itself is temporary, at
`/tmp/current14-standard-fresh-source-20261104`. These are source-declared
observations, not a Lean build or authoritative full dependency discovery.
A later [follow-up audit](source-audit-followup.json) at workspace HEAD
`cf3e786db8dcb5d59cc13cc59e7cf7f23562c141` also exited 0 with all 1,000
sources matching. This is a point-in-time observation, not a guarantee that
the files will remain unchanged throughout a later build.

The read-only [`preflight.py`](preflight.py) exited 0 and records its
[observation](preflight-observation.json): all 1,000 workspace and frozen
source hashes matched; the 14,764 declared external guards and 1,540
fresh-Foundation artifacts matched the existing guarded provider receipt;
the nine project namespace names had no fallback provider artifacts. Free
space sampled **12,435,927,040 bytes**. These point-in-time checks cannot
exclude mutations between observations or establish package-transitive and
dynamic ancestry. The original Foundation receipt records the inner Lake
exit, but its outer wrapper exit was not captured; the subsequent provider
artifact audit has its own recorded scope.

For a footprint reference only, an existing overlay had 995 of the 1,000
target `.olean` files with a combined logical size of 449,832,856 bytes.
Those files are **not** used as build inputs. Other artifacts, logs, temporary
files, source changes and concurrent disk use make that number neither a
reservation nor an upper bound. A historical 1,210-module source build
recorded 11,132 seconds of summed Lean compilation time; the target's total
duration is uncertain.

[`run.py`](run.py) prepares a single fresh-project build using the existing
guarded `fresh-project-closure/rebuild.py`, with an initially empty project
object root and the one fresh Foundation provider. It refuses to start if a
Lean process is already running. It records an actual child PID, command,
log, state and exit, samples disk space and the builder's progress every ten
seconds, and terminates its own process group at six hours or if a sample
shows less than 4 GB free. These are sampled protections, not disk
reservations or a guarantee against sudden external disk use. The run is
separate from the preflight. A successful single pass would not itself be a
paired replay or authenticate inherited package-transitive and dynamic
dependencies.

The separate [`busy-control.py`](busy-control.py) created a temporary process
with the Linux process name `lean`, then invoked the launcher. The
[recorded control](busy-control-observation.json) exited 0 after confirming
that the launcher refused with exit 1 and left all build paths absent. This
tests the launch refusal only, not successful compilation or disk-stop logic.

After the shared Lean slot became available, the source and provider audits
were repeated, and the build was launched. The
[source audit](source-audit-at-launch.json) at HEAD `bd80d5c669` again
matched all 1,000 tracked sources; the [provider audit](provider-audit-at-launch.json)
again passed, with 12,419,260,416 free bytes. Tool session `7009` and builder
PID `48282` were observed running. The [launch observation](launch-observation.json)
records the live process and initial progress; it is **not** a completion
receipt. The subsequent terminal result is recorded below.

The build later completed: launcher session `7009` actually exited 0 after
8,548.83 seconds, and the watchdog and builder both reported `PASS`,
`CURRENT_AT_FINAL_CHECK` and empty workspace source drift. The [terminal
observation](terminal-observation.json) records that actual exit and state
hashes. A separate [independent artifact audit](../../reviews/current14-fresh-base-independent/README.md)
exited 0 and checked all 1,000 sources and outputs, 4,179 direct input edges,
11,050 input companion guards, 1,540 Foundation artifacts and four exact
endpoint axiom reports. This is one build plus an artifact audit, not an
independent second Lean replay; inherited package-transitive, dynamic and
between-observation ancestry remains outside the audit. The structured
printed-port link is separate and has not yet been built coherently.

For reference, the launch command was:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/current14-standard-fresh-rebuild-preflight/run.py
```

The launcher refuses existing output or observation paths. Its live/final
observation will be `run-observation.json`; its full process log and object
tree will be under `/tmp/current14-standard-fresh-build-20261104*`. If it is
live, inspect that process and state rather than launching another copy.
Any workspace source changes during the build are recorded by the existing
driver; a successful but drifting run is historical, not source-current.

SHA-256: snapshot manifest
`1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749`;
source audit `9470215579772dc0b6eb339198b1aa103292c478cecaed449e92a81192c9293d`;
provider preflight `732016eeea309b6f24fc82170ceee85c0b74f8a6187c021c36bdcccb31e0ed64`;
launcher `790a4b13f96f5cd544981aab6bdc7ae9e573a32f14195505551e191f0ee0a212`.

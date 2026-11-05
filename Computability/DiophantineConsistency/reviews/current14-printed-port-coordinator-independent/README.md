# Independent static review of the proposed extension coordinator

Reviewed the frozen coordinator `f898dad6…ce480b`, terminal verifier
`005b0f48…1061ac`, controls `10bba53b…d93d`, and retained synthetic controls
receipt `78823481…6762c`. Run `python3 -I -S -B audit.py` from this directory
to check their exact hashes, the receipt's linkage and 13 reported controls.
The local [result](result.json) records that read-only cross-check. No Lean,
coordinator, extension, or synthetic controls were launched in this review.

**Process-lifecycle finding:** the pinned extension driver's `run_module` starts
each Lean compiler with `start_new_session=True` but has no `finally` that
stops and reaps it if monitoring itself raises after launch. For example,
`shutil.disk_usage` can raise. The driver can then record failure and exit
while its separately sessioned Lean process remains alive. The coordinator
waits for the driver, not every compiler session, so its monitor-failure
handling does not establish that all descendants have stopped. This does not
produce a terminal PASS, but an operator must check for surviving Lean before
any subsequent launch; waiting for the driver is insufficient. The synthetic
fake-child control covers the outer monitor exception only, not this inner
failure. A separately revised driver is being prepared; no revised version was
reviewed here.

The successful outer path records `proc.wait()`'s actual driver return code and
requires zero before verifying terminal state, 61 ordered successful rows,
source/output/log hashes, declared direct import routes, base overlay and
external guards, complete file inventory, and absence of external namespace
shadows. It repeats preflight and relevant guard checks around validation.
The receipt includes positive controls and rejection cases, but does not
exercise a real successful extension or prove every operational failure path.
The terminal audit is not a filesystem snapshot: modifications between
checks, imports executed before source hashing, external transitive or dynamic
ancestry, and concurrent process starts are outside its guarantee. Idle-slot
and resource checks are observations, not locks or continuous reservations.
The child driver provides a per-module memory setting and time/disk checks;
the outer monitor samples memory and disk without automatic low-memory stop.
No result here proves an endpoint theorem, a fresh build, or iPRA equivalence.

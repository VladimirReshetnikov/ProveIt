# Independent source review of the base-only endpoint runner

Reviewed [`runner.py`](../../research/current14-mf-base-only-endpoint/runner.py)
SHA-256 `1013bbda00819d45a8f5e652ad81b025867d7697e0e395c373e10f3b2427f7f8`
and the exact pinned client, driver, guard, dependency-policy and owned-session
helper sources recorded in [`result.json`](result.json). The prior missing
base-library inventory and empty external-namespace shadow checks have been
addressed: before and after the clients, the runner authenticates the base,
walks its full file inventory with errors propagated, rejects symlinked
subdirectories and external namespace roots, and checks the private client
output inventory and project/external namespace roots. A simple independent
current inventory listing also matched the 1,000 recorded base files.

Each client is copied from a pinned source and compiled with a private output
root followed by the authenticated base and package overlay. `lean --deps` and
compile executions are separately monitored; their actual child exits,
owned-session receipts, samples, direct import paths/producer guards, logs,
output hashes and source hashes are retained. Unexpected direct providers,
missing declared imports, warnings, errors, `sorryAx`, unexpected axiom-report
names/order, and axioms beyond `propext`, `Classical.choice`, `Quot.sound`
are rejected. The final client is required to report the exact named endpoint.
The owned-session helper waits for observed session drain; monitor failure may
wait indefinitely and escaped sessions, forced process termination, transient
races and kernel-level failures remain outside its guarantee.

[`audit.py`](audit.py) rechecks the exact pinned inputs and independently
reruns only the temporary, non-Lean controls. Their positive and negative
cases cover inventory mutation, namespace shadows, symlinked directories,
walk errors, report order, unexpected axioms, `sorryAx`, warnings and errors.
No Lean process or client runner was launched during this review. The controls
do not exercise the real Lean build or prove full transitive/dynamic provider
provenance. An external observer must retain the actual outer runner exit; a
runner `PASS` is not by itself an observed successful process exit. No endpoint
or TeX/PDF semantics claim follows from this review. Run the audit with
`python3 -I -S -B audit.py`.

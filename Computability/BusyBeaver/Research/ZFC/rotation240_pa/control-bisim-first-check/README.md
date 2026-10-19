# First concrete internal bisimulation check: memory failure

The unchanged `ControlBisimRotation240` source was checked against the fresh
`DagControl254` provider and its exact prerequisite closure. The compiler
terminated after 59.297 seconds with exit code −6 and a Lean
`memory_exception` at the interpreter. The [raw log](source.log) and
[actual record](verification.json) retain the diagnostic. This was not a
timeout, a failed mathematical assertion or a counterexample.

The run kept the source's existing recursion limit 100,000 and unlimited
heartbeats, with one thread, a 4,096 MiB memory limit and a shared 120-second
source-and-audit deadline. All input/provider postchecks passed. No fresh
proof object was accepted and the planned eight-probe, ten-caller audit
was not run. The unit remains unverified by this check.

The [history](history.json.gz) preserves the original source, audit draft,
guard, boundary and actual failure. The next approach splits finite
certificate checks into separate modules while preserving the literal
tables, complete certificate coverage and public halting-equivalence
statement. No larger memory limit or successful split run is claimed here.

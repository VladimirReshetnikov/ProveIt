# Independent 24-module window builder prelaunch review

The exact builder bytes from `e965ddc7d5` have SHA-256
`4a90711717997a2424faaf67d9010cee16c1ef792ef5f652461b52f861c82655`.
The source and pinned parent/freezer audits were inspected without launching
Lean. Independent loader-clean preflight session 88859 actually exited 0 with
24 modules and one free-space sample; no real window build was started. The
[receipt](CHECK.json) binds the retained controls and observed exits.

An in-memory test drove the actual builder loop using a substituted fake
compiler: 48 successful child compiles and direct-import checks completed in
two sibling overlays, a synthetic warning was accepted, and a separate fake
`sorryAx` output was rejected without a success receipt. The fake child saw
no inherited `PYTHON*` variables. A separate positive sitecustomize control
demonstrated the hook works, and isolated Python suppressed it. The fake
compiler is not the pinned Lean executable and does not establish real Lean
or dependency-query success. Controls also rejected nonisolated/optimized
invocation, bad output path and source pin, a missing module, cyclic closure,
changed object and newly introduced companion.

The reused monitor's fake-child controls passed for missing/transient RSS,
exit races, an injected exception and external SIGTERM with a same-group
descendant. Additional controls injected sampled RSS, disk and timeout
failures. These show sampled leader RSS, host free-space checks and cleanup of
the verified group only in the tested cases, not hard quotas, whole-process
accounting, escaped descendants, PID reuse, forced wrapper termination or
continuous mutation protection. Direct `lean --deps` queries use a timeout
but do not run through the sampled monitor.

**A trusted clean initial native-loader environment is required.** An actual
harmless `LD_PRELOAD` constructor ran before the isolated Python driver's
bad-output guard. The driver strips listed loader variables for Lean and
dependency-query children, but the initial interpreter and `verify_audits`
subprocesses inherit the launching environment. `python -I -S` prevents
Python site injection, not native-loader injection; clear such variables
before starting the interpreter and its audit children.

The driver checks its own bytes and pinned inputs at defined points; it does
not enforce Git HEAD stability. Enforce any stable-HEAD window externally.
It accepts warnings and allows zero printed axiom reports; classify the real
run's warnings and reports during a later independent artifact audit. Missing
reports do not establish axiom-freedom. The prefix lacks a complete printed
axiom inventory; package-transitive/dynamic ancestry and the original
Foundation outer-wrapper exit are inherited qualifications.

Within these conditions the driver is suitable for a coordinated attempted
build. This is not a build receipt, actual-zero theorem, rank-phase theorem,
or iPRA proof.

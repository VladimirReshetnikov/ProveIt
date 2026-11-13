# Independent 20-module prefix builder prelaunch review

The exact builder bytes from `d486458873` have SHA-256
`881f806b91c37ce596130a19e74a3c605c0ea3c11379f68b1f59bf641dada204`.
The source and pinned parent/freezer audits were inspected without launching
Lean. Independent preflight session 14811 actually exited 0 with 20 modules
and one free-space sample; no real prefix build was started. The
[receipt](CHECK.json) binds all retained control results and actual observed
exits.

An in-memory test drove the actual builder loop using a substituted fake
compiler: 40 successful child compiles and direct-import checks completed in
two sibling overlays, a synthetic warning was accepted, and a separate fake
`sorryAx` output was rejected without a success receipt. It also checked the
fake child received no inherited `PYTHON*` variables; a separate positive
sitecustomize canary demonstrated the test hook works, and isolated Python
suppressed it. The fake compiler is not the pinned Lean executable and this
test does not establish that the real compiler or real dependency queries
will succeed. The guard controls rejected nonisolated/optimized invocation,
bad output path and source pin, a missing module, cyclic closure, changed
object and newly introduced companion.

The reused monitor's real fake-child controls passed for missing/transient
RSS, exit races, an injected exception and external SIGTERM with a
same-process-group descendant. Additional controls injected sampled RSS,
free-space and timeout failures. These demonstrate only sampled leader RSS,
host free-space stops and cleanup of the verified group in the tested cases;
they do not cover hard quotas, whole-process-tree accounting, escaped
descendants, PID reuse, forced termination of the wrapper or mutations between
checks. Direct `lean --deps` calls have a subprocess timeout but are not run
through the sampled monitor.

**Initial loader environment is a launch prerequisite.** A harmless native
`LD_PRELOAD` constructor actually ran before the isolated Python driver's
bad-output guard. The driver sanitizes listed loader variables for the Lean
and dependency-query children, but its initial interpreter and `verify_audits`
children inherit the launching environment. `python -I -S` prevents Python
site injection; it does not isolate the native loader. Start from a trusted
environment with loader injection variables absent before the interpreter and
audit subprocesses start. Other startup and operating-system trust remains
inherited.

The driver hashes its own bytes and pinned source/provider inputs at defined
points; it does **not** pin or recheck Git HEAD. Any stable-HEAD requirement
must be enforced externally. It accepts compiler warnings and allows no
axiom reports; the fake loop confirmed both behaviors. A successful real
replay requires independent classification of all actual warnings and axiom
reports, and missing reports cannot establish axiom-freedom. Parent/provider
audits and the frozen source manifest remain point-in-time evidence, not
continuous mutation protection. The original Foundation outer-wrapper exit,
package-transitive and dynamic ancestry remain inherited qualifications.

Within these explicit prerequisites the reviewed driver is suitable for a
coordinated attempted prefix build; this review is not a build receipt, an
actual-zero theorem, a rank-phase theorem, or an iPRA proof.

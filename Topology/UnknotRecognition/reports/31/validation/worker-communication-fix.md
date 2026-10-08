# Regina worker input-retention compatibility repair

## Reproduced failure

The complete maintained module batch ran 720 tests before this repair. The
existing `test_communication_retains_input_across_polls` was its sole error.
That test launches a child which delays reading for 0.12 seconds, sends a
500,000-character payload, and expects its complete echo and a stderr marker
within the unchanged three-second local allowance. It failed again in an
isolated rerun. Raw evidence is retained in
`module-logs/test_normal_surface.log` and
`normal-communication-isolated.log`.

The earlier implementation supplied the payload on the first
`Popen.communicate(payload, timeout=...)` call and retried with `None` after
`TimeoutExpired`. In the measured CPython 3.12.14 standard library,
`_communicate` calls `_save_input(input)` but registers stdin for writes only
when the current argument satisfies `self.stdin and input`. Thus, after a
partial initial write, retaining the original payload internally does not
ensure that retries with `None` transmit its remainder. The child cannot
finish reading its request. This diagnosis concerns the inspected runtime;
it is not a claim about every Python release or platform. The relevant local
source branch is preserved in `python-communicate-input-branch.txt`.

## Repair and resource semantics

`fastunknot/normal_surface.py::_invoke` now starts a single daemon thread
whose sole communication operation is `child.communicate(payload)` without
an internal polling timeout. The caller waits on a completion event in
bounded intervals while running the existing caller-provided cancellation
check and enforcing the same local deadline. The callback remains on the
calling thread. A communication `OSError` becomes a worker failure; a
caller's cancellation exception continues to propagate.

Every path after successful child creation is protected by cleanup,
including event construction, thread construction and thread startup.
Cleanup kills a live child, waits for it, joins a successfully started
communicator, and then closes all three pipes. In particular, a thread setup
failure never attempts to join a thread which was not started. This retains
the controlled direct-child contract used by the Regina worker. It does
not add a general-purpose process-tree supervisor for arbitrary programs
which leave grandchildren holding inherited pipes.

The external-engine trust statement is unchanged. Worker timeout, invalid
output or engine failure remains inconclusive; the repair neither promotes
an incomplete worker run to a knot decision nor turns its answer into an
independently verified normal-surface certificate.

## Review and verification

An independent agent reviewed the ownership of communication, event
publication, caller-thread callbacks, cancellation, child reaping, joining,
pipe closure and setup failure. That review identified and closed a scope
gap where event/thread constructors had initially preceded the cleanup
block. The final code places those constructors inside the protected block.

The existing long-input, local/global cancellation, malformed-worker,
external-verdict and CLI tests are unchanged. One added combined test
injects a communicator `OSError`, event-constructor failure, thread-constructor
failure and thread-start failure. It checks that each real child is reaped
and all pipes close, that communication receives the payload exactly once,
and that the polling callback runs on the caller thread.

With the optional Regina 7.4.1 distribution enabled, the final affected
module passes 9 tests in the reported 2.732 seconds. The public integration
suite then passes 6 tests in 0.010 seconds. The exact logs and source hashes
are in `normal-surface-after-fix.log`, `integration-after-worker-fix.log` and
`final-validation.json`. Final discovery contains 721 tests: 712 retained
passing tests in the 82 unchanged modules plus the nine-test affected
module. The integration rerun duplicates six of the retained tests.

This repair is a correctness and compatibility fix discovered during
integration validation. It is separate from the three mathematical
performance primitives and is not included in their timing comparisons.

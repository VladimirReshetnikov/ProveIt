# Portable worker-pipe compatibility correction

The initial complete-suite run exposed an unchanged baseline defect in
`normal_surface._invoke`: after timing out during delivery of a 500,000-byte
request, the retry stopped writing the remaining input on the installed
Python 3.12.14 runtime. Both the current tree and pinned baseline failed the
isolated test in 3.002 seconds. Their source and test files were byte-identical
to commit `8a95834940cf77cdab1b39571ffc102ca8b6bede`.

The diagnostic recorded a 65,536-byte pipe capacity and an input offset that
remained at 65,536 across every retry. The runtime retained the input bytes,
but its selector registered stdin only when the current `communicate` input
argument was truthy. Passing `None` on retries therefore left the rest unsent
and never delivered EOF. An uninterrupted communication control delivered all
500,000 bytes and completed in 0.135 seconds. These observations are preserved
in `normal_surface_diagnosis.json`, the isolated logs, and the runtime-source
excerpt; that evidence describes the source before this correction.

## Correction

`_invoke` now gives one dedicated non-daemon thread ownership of exactly one
`child.communicate(payload)` operation. The main thread waits on an event for
at most 50 milliseconds per poll, checks its local deadline, and invokes the
existing global cancellation callback. A completed communication remains
subject to the final deadline and cancellation checks before publication.

Worker exceptions are transported to the main thread. Communication `OSError`
values retain the existing `NormalWorkerError` mapping; exceptions raised by
the caller's check remain caller exceptions. Failure cleanup kills and reaps
the subprocess, joins its communication thread, and only then closes its
streams. Synchronization objects are prepared before process launch, and
thread construction/start failures are covered by process cleanup.
Specifically, `RuntimeError` or `OSError` raised by `Thread.start` is mapped to
`NormalWorkerError` after cleanup, so the external-engine wrapper returns
`INCONCLUSIVE`. The catch surrounds only thread startup and cannot absorb
exceptions raised by the caller's check.

This uses public `subprocess` and `threading` interfaces. It sends no repeated
input and makes no use of private subprocess buffers, offsets, selectors or
thread internals. The mathematical recognizer, Regina protocol, returned
verdicts and external-engine trust statement are unchanged.

## Validation

The previously failing 500,000-byte communication test passes unchanged. One
new test cancels a request while the child delays reading a two-million-byte
payload. It verifies that cancellation returns, the child is reaped, every
created communication thread is stopped, and all three streams are closed.

The complete normal-surface test file passed: **9 tests in 2.805 seconds**.
This includes actual Regina worker verdicts, the CLI, global deadlines, local
cancellation, failure handling, and the new blocked-payload test. The focused
Jones tests also passed: **13 tests in 0.378 seconds**. Logs are
`normal_surface_thread_fix_tests.log` and `spin_after_pipe_thread_tests.log`.
The environment used Python 3.12.14 and Regina 7.4.1. No whole-suite rerun was
performed for this subtask; the parent integration owns that gate.

After adding both thread-start failures to the existing error-path test, the
normal-surface file passed again: **9 tests in 2.841 seconds**, with verified
subprocess exit code zero. The final log is
`normal_surface_thread_start_verified.log`. An earlier tool capture ended
mid-test without a summary; that incomplete log is retained as
`normal_surface_thread_start_tests.log` and is not counted as a passing run.

The exact source before correction is retained as
`normal_surface_before_pipe_thread.py`. Its SHA-256 and the corrected source
hashes are recorded in `normal_surface_thread_fix_report.json`.

## Scope and limitation

This is a compatibility correction separate from the mathematical results
and invariant performance measurements. It does not claim a new running-time
bound or faster unknot recognition.

The cleanup contract concerns the directly controlled worker. That worker
must not leave descendants inheriting its standard pipes, since such a
descendant could keep a reader waiting after the direct child is killed.
The maintained Regina worker launches no Python subprocesses. The correction
does not provide portable process-tree isolation. Its interfaces are standard
and portable, but this validation ran on Linux, not Windows or macOS.
Polling is cooperative; total cancellation latency also includes scheduling,
the callback, and subprocess/thread cleanup.

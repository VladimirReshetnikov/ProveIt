# Sampled process monitor prototype

`monitor.py` starts one child in a new process group after creating a fresh
run directory. It provides `MONITOR_OUTPUT` (a nonexistent child-output path)
and `TMPDIR` inside that directory, combines child output in `child.log`, and
records the actual leader exit in `terminal.json`. Defaults sample host free
space against 4 GiB and logical file sizes in the run directory against
512 MiB. A sample below the free threshold or above the budget stops the
process group with TERM followed by KILL after the grace period. SIGINT and
SIGTERM request the same shutdown. A leader which exits while descendants
remain in its group is not reported as a successful clean exit.

**These are sampled stop thresholds, not a quota or continuous reserve.**
Bytes written between samples may overshoot; logical sizes omit filesystem
overhead and files behind symlinks. The monitor does not confine absolute or
other external write paths, account for other users, guarantee disk space, or
kill a descendant that deliberately escapes into another session. SIGKILL of
the monitor cannot trigger cleanup. It must not be represented as an
aggregate-write cap or used as the sole provenance guard. Child commands must
honor `MONITOR_OUTPUT` and `TMPDIR`; the ordinary Lean driver still needs its
own source, provider, isolation, direct-import and output checks. Read the
reviewed build plan and obtain separate driver review before a real run.

The isolated toy controls are run with:

```
python3 Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/difference-ring-build-plan/monitor/test_monitor.py
```

The last actual invocation (session 47065) exited 0 and printed:

```
PASS reaped procfs ENOENT and ESRCH controls
PASS actual success and fresh-path guard
PASS preflight stop
PASS disk process group terminated
PASS budget process group terminated
PASS successful leader with lingering descendant rejected
PASS actual interrupt and descendant cleanup
PASS_MONITOR_TOY_CONTROLS
```

The success and interrupt cases launch real Python child processes. The
disk and budget controls inject sample values through the imported test API;
there is no mock-sensor option in the production CLI. Descendant tests include
processes which ignore TERM and are killed with their group. These tests do
not launch a Lean project build or prove behavior under concurrent or escaped
writers. The exact script SHA-256 values for the observed run are:

- `monitor.py`: `861ab896f3b82fce63352bf26e8ac7f06d969a0472f01b1065fdba51a3946b50`
- `test_monitor.py`: `1e00d4d810a222022ec9e03bba09e543ce4e6e3b65738ca769f168cc91e41ea6`

`paired.py` is a separate, unlaunched coordinator for two sequential monitored
siblings. It passes each monitor's fresh `child-output` to the guarded builder,
requires the actual monitor exit 0, builder exit 0 and builder `state.json`
status `PASS` before starting the next sibling, then invokes the existing
comparator as a separate process. It records complete process logs and their
hashes, monitor and builder exits, terminal states, comparator result and
hashes. The comparator is called only after both siblings pass; it must itself
return exit 0 and `MATCHED_PASS`. A signal to the coordinator is forwarded to
the active monitor, which stops the builder group. If the monitor does not
exit within the escalation interval, the coordinator checks the builder PID,
its recorded Linux process start ticks, process group and session before
attempting SIGKILL on that group, and kills the monitor group. If identity
cannot be checked, it reports cleanup as unconfirmed instead of signaling an
unverified PID. A builder exit not observed by its monitor remains null.
An uninterruptible task may not reap even after SIGKILL; the coordinator
stops waiting and marks the monitor exit unobserved. PID checking is not an
atomic pidfd group operation and does not cover processes which escape the
group. It does not prove the
builder, provider, source freeze or comparator correct, and its comparator
runs outside the sibling's sampled-size budget. The sampled host-space and
write-scope limitations above remain in force. The configurable executable
paths exist for testability and must be pinned and separately reviewed before
real use.

The separate paired toy test, using fake builder and comparator executables,
ran in actual session 96209 and exited 0 with:

```
PASS missing or mismatched builder identity remains unconfirmed
PASS pair, actual exits and logs
PASS author failure prevents peer and comparison
PASS sampled stop prevents peer and comparison
PASS peer failure prevents comparison
PASS comparator failure retained
PASS coordinator interruption terminates monitored descendant
PASS stalled monitor escalates verified builder group and reports unobserved builder exit
PASS unverified builder remains unconfirmed and toy harness cleans up
PASS_PAIRED_TOY_CONTROLS
```

These are real subprocesses; the budget stop writes a small test file and
waits for sampling. The test does not invoke Lean, the real provider, or a
real project comparison. Hashes for this observed test are:

- `paired.py`: `694c9807f788b8367419c3f86919c2af9816c0fa6b2c7849bb456dbc7ff65476`
- `test_paired.py`: `966e6d8eb9b87c9c1954045e154d84f35bed2e28e80bd357f52d330f04192196`

An independent prior monitor-toy run exited 1 when a process was reaped
between checking for and reading its `/proc/<pid>/stat` file. The exact
reported traceback excerpt and prior test source are in `observations/`.
An initial correction caught `FileNotFoundError`, but the first repeated
run then exited 1 with `ProcessLookupError` for the same read. That second
failure and its preceding test source are also recorded under `observations/`.
Both test suites now treat either ENOENT or ESRCH on that read as a dead
process; deterministic controls exercise both exceptions. A separate
10-invocation monitor-toy repetition then exited 0 in session 71737. The
monitor and coordinator implementation did not change for this test-only
correction.

## Prewrite and optimized-mode correction

Independent controls found the original wrappers could create output beneath
protected input trees before rejecting an invalid run, and that the historical
builder can pass invalid inputs under `PYTHONOPTIMIZE=1` because that disables
its assertions. The revised coordinator validates snapshot/provider pins and
requires existing absolute provider root and overlay paths before output
creation. Both entrypoints reject protected overlap, existing destinations,
noncanonical paths and symlinked ancestors, with point-in-time rechecks; the
standalone monitor protects named builder inputs and caller-supplied
`--protect` roots. These guards are not adversarial TOCTOU protection.

Both wrappers reject optimized Python and any nonempty `PYTHONOPTIMIZE` before
writing; the monitor also removes that variable from its child environment.
The coordinator invokes the builder with `sys.executable` and no `-O` flag.
The historical builder was not changed and remains unsafe if called directly
with optimized Python. The coordinator pins the shared `path_guard.py` along
with its other executable inputs.

Actual revised monitor session 95826 and final paired session 49728 both exited 0.
Their controls include no-write rejection of protected/symlink paths, bad
input pins and an inherited optimization variable; successful paired toy
builders assert `__debug__` and the absence of `PYTHONOPTIMIZE`. These are
still toy controls, not an actual project replay. The final observed hashes are:

- `path_guard.py`: `9af0852abe419dee3fa83a57aa8fbdb3584285c8c40a229c9ef041f610375173`
- `monitor.py`: `bcb54868a78911f470e1ab833255b67e8f26d82fc7133eb0ddc5e663ef4770f8`
- `paired.py`: `ab9a2787e4fb99f9c201280e1219e48a2bf6f7c8a2e8f78049743b3dce282ebb`
- `test_monitor.py`: `52650f400f92adc9b83030da0ae8a4488cc32a1e94c1ea15ee0e652551cc74ed`
- `test_paired.py`: `6513363589dc07e2d46c715a07943ff1b4ab734dd11f601b7e3b46e1854f835a`

## Isolated Python process chain

The earlier wrapper hashes and toy sessions above are historical. The
coordinator and monitor now require `-I -S` at their actual CLI entrypoints.
The coordinator invokes the monitor through an isolated `runpy` bootstrap
which inserts only the pinned monitor script directory, and invokes the
stdlib-only historical builder and comparator with `-I -S`. A reviewed outer
launcher must itself use isolated startup and remove inherited `PYTHON*`
variables before starting the coordinator; a direct non-isolated invocation
can execute Python startup hooks before a script rejects it. Non-Python
runtime, executable, package and dynamic-load trust boundaries remain.

Revised monitor toy session 6855 and paired toy session 57209 actually exited
0. The paired mock builder, comparator and stuck monitor assert isolated and
no-site flags, and the ordinary stop/cleanup/guard controls still pass. These
are fake children, not a full project replay. Final script hashes:

- `monitor.py`: `f83085ddc84b9376d934cfbc4b29cd28b91f10a7f1ac28fd372e276b5cf542ee`
- `paired.py`: `b3eb4021ae3d8797adcb796bcbe3613a9363ea5b4917d85173e92e27c08f9910`
- `test_monitor.py`: `6ef9bb779def89ba1d2705e1e3c0f6a26c641d4fe193f01237eb49aaec178fb5`
- `test_paired.py`: `f3de7241071deeae8be007f208b9efa58fb27d36cf04b44354f436a6ac3f04e2`
- `path_guard.py`: `9af0852abe419dee3fa83a57aa8fbdb3584285c8c40a229c9ef041f610375173`

A subsequent actual full-chain canary test, session 73693 exit 0, first
confirmed a temporary `PYTHONPATH/sitecustomize.py` hook executes in a normal
Python control, then observed that the isolated coordinator, monitor, fake
builder and fake comparator completed without executing that hook. The
updated `test_paired.py` SHA-256 is
`dec96710caf9d0091ef65adc3aceb0d07f9d0f4ae7145a8904d59c937ed98219`.
This tests the Python startup chain only, not non-Python environment or
runtime trust and not a real project rebuild.

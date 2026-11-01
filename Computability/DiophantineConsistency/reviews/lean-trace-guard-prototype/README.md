# Prototype syscall trace guard for a fresh Lean replay

[`trace_guard.py`](trace_guard.py) classifies successful `open`, `openat`,
`openat2`, `execve` and `execveat` events in a supplied Linux `strace` log.
It requires this exact tracing form:

```text
strace -f -qq -yy -xx -s 4096 -e trace=open,openat,openat2,execve,execveat -o module.trace ...
```

The caller provides a JSON policy with `roots`, each containing an absolute
`path` to an existing directory and a `role`. The guard resolves symlinks,
requires every observed target to fall under a permitted resolved root, checks
the kernel's returned file-descriptor path when present, hashes regular files
after the run, and fails on malformed, incomplete, unresolved, unexpected or
unsupported events. Relative `openat` paths require an absolute decoded
`-yy` directory annotation. Special files require exact entries in the
optional `special_paths` list and receive no hash. The filesystem root `/` is
rejected unless an explicit smoke-test override is set.

Run `python3 test_guard.py` after moving aside an existing test receipt. Its
14 controls include unresolved relative/dirfd paths, descriptor mismatch,
symlink escape, unexpected dynamic library, incomplete and resumed calls,
truncated or unsupported encoding, a real Lean invocation, and an actual
shared library loaded by `ctypes`. The broad `/` policy in the smoke test is
deliberately permissive and is not a production acceptance policy.

This tool has **not** been integrated into a project replay. Its report is a
post-run observation of selected syscall types, not proof of compile-time file
identity or complete provenance. It does not authenticate the trace's process
exit or command, detect files changed and restored during the run, track
inherited file descriptors or every possible operation such as `stat`,
`io_uring`, or memory passed by another process, or establish the correctness of
the tracer, kernel, toolchain and dependencies. The caller must separately
pin the trace invocation, record and verify its exit, preserve raw logs, guard
inputs before and after use, and distinguish inherited package and system
libraries from independently rebuilt inputs.

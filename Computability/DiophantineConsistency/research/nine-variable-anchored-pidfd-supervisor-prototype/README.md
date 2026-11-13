# Synthetic anchored-session and process-handle prototype

This is an experiment only. It does not run a Lean reader, a project worker,
the real launcher, or a production resource supervisor. The frozen v3 runner
continues to use numeric PID signaling and retains its documented PID-reuse
risk. This prototype has not had an independent review and is not a drop-in
replacement or a proof of OS-level safety.

On x86_64 Linux, it opens `/proc/<pid>` as a directory first, reads `stat`
relative to that same open descriptor, checks the recorded session ID, and
calls syscall 424 (`pidfd_send_signal`) on the descriptor. Thus the signal is
addressed to that opened process handle, rather than to a numeric PID obtained
in an earlier scan. The experiment never calls numeric `kill` or `killpg`.
The [Linux pidfd_send_signal manual](https://man7.org/linux/man-pages/man2/pidfd_send_signal.2.html)
describes a `/proc/<pid>` directory descriptor as a supported process reference.

The parent uses `waitid(..., WNOWAIT)` and intentionally leaves its owned
session leader unreaped until the rest of that session has been observed gone.
The intended rationale is that the unreaped leader anchors the session's
numeric identifier while proc descriptors are opened and checked. This kernel
lifecycle assumption, the full enumeration protocol and the scope of
`waitpid` for adopted descendants require independent analysis. The test
assumes a dedicated supervisor process with no unrelated concurrently created
children. It does not establish correctness in the presence of concurrent
reapers or PID-namespace changes.

The test creates only temporary Python sessions. Its child creates a grandchild
in a different process group within the same session. Controls cover an actual
injected monitor exception, leader exit, timeout, and one injected signal
error; they require both descendants to be reaped before the leader. A separate
session bystander must survive. The signal-error control records a failure
even though later cleanup succeeds. The test uses Linux child-subreaper mode.
`result.json` is the actual synthetic run output. Run with
`python3 -I -S -B check.py`.

The prototype is x86_64/Linux-specific; syscall availability and `/proc`
semantics may differ across kernels or configurations. A scan, handle open,
stat read, signal, or reap may fail. The prototype records unexpected scan and
signal errors, but its own test-cleanup path is not a complete exception-safe
supervisor. A process that leaves the session can escape detection. Supervisor
SIGKILL or host failure can interrupt cleanup. Sampling misses resource spikes,
and this prototype has no memory, disk, time or provider guards suitable for
an actual batch. The controls do not force PID reuse, prove freedom from every
race, test pid namespace transitions, or test arbitrary adversarial workloads.

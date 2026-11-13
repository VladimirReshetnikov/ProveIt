# Stop-and-rescan assessment for the header reader

A bounded stop-and-rescan loop could reduce the likelihood of a descendant being
missed during cleanup, but it does **not** prove that cleanup found every live
descendant. I do not recommend integrating it into the reviewed traversal as an
identity-safe or complete-containment solution. A synthetic prototype could
measure its behavior with a finite, cooperative forking workload, but its
passing result would not close the general enumeration race.

A plausible best-effort procedure would leave the session leader unreaped,
open a stable `/proc/<pid>` descriptor before checking that process's session,
use that descriptor to send `SIGSTOP`, and repeatedly enumerate the session
until observed live members have acknowledged a stopped state. It would need a
strict deadline and bounded memory use, retained inspection and signal errors,
an exception-safe cleanup path, and a way to kill stopped processes without
resuming them. SIGKILL via the same stable process handles is a candidate;
termination and reaping must still be observed. A process in uninterruptible
sleep may not promptly acknowledge a stop or a kill, so timeout must remain a
failure, not a success receipt. Thread groups and thread states also need
careful treatment: seeing the leader thread stopped alone need not establish
that every thread has stopped.

Repeated scans cannot themselves certify quiescence: an as-yet-unseen live
member can fork after its position in a `/proc` directory iteration has been
passed. Its child can in turn fork before it is discovered and stopped. This
can recur even if two scans happen to report the same stopped members. An
unseen process may also change session, while an external actor may resume a
stopped process. A workload known independently to make only finitely many
forks, never escape, and not receive SIGCONT would make the technique useful
operationally, but that is an explicit behavioral assumption, not a conclusion
of the scan or of the existing Lean-header evidence.

On this host, read-only inspection found a cgroup v2 mount and current cgroup
`/user.slice/user-1000.slice/session-6976.scope`. Its directory and
`cgroup.freeze`/`cgroup.procs` files are root-owned and not writable by the
`codex` user; `cgroup.kill` is root-write-only. No cgroup control was changed.
The session cgroup is shared and must not be frozen or killed. A separately
delegated child cgroup with atomic kernel freeze or kill and independently
reviewed setup might offer stronger containment, but has not been provided or
validated here.

No actual header traversal, Lean process, real review gate, or cgroup mutation
was launched for this assessment. The existing v3 runner and separate
anchored-handle prototype remain unchanged.

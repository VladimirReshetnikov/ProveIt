# Independent review: synthetic anchored process-handle prototype

**The stated synthetic controls reproduce; this is not a production supervisor
or a PASS gate for the header traversal.** The review freezes the exact
[author source](author-check.py), [description](author-README.md) and
[result](author-result.json). It ran no Lean reader, project worker, real
launcher or traversal, and created no review gate.

For each numeric `/proc` entry, `scan` opens the process directory, reads
`stat` relative to that same descriptor, checks its session ID, and passes
the descriptor—not the earlier numeric PID—to syscall 424
(`pidfd_send_signal`). The source has no numeric `kill`/`killpg` or
`Popen.kill`/`terminate` fallback. Linux's
[pidfd_send_signal manual](https://man7.org/linux/man-pages/man2/pidfd_send_signal.2.html)
explicitly permits an open `/proc/PID` directory as a process reference;
the [kernel proc documentation](https://www.kernel.org/doc/html/latest/filesystems/proc.html)
states that operations on an old open descriptor do not act on a different
process later assigned that PID. These statements are Linux-specific and
depend on the running kernel and namespace/proc setup. The code reads
`starttime_ticks` but does not compare it; identity of the signal target here
comes from the opened proc descriptor and its descriptor-relative stat read.

The session leader is created with `start_new_session=True`. During monitoring
the parent uses `waitid` with `WNOWAIT`, so it observes but does not reap a
terminated leader. The [waitid documentation](https://man7.org/linux/man-pages/man2/waitid.2.html)
states that `WNOWAIT` leaves the child waitable; an unreaped zombie retains
its PID, supporting the anchor argument while no other reaper consumes it.
The [setsid documentation](https://man7.org/linux/man-pages/man2/setsid.2.html)
states that a new session leader's session ID equals its PID. This reasoning
assumes the leader remains the supervisor's waitable child, normal SIGCHLD
handling, no concurrent reaper, stable PID-namespace/proc semantics and a
supported kernel. A child-subreaper adopts orphaned descendants under the
[documented Linux behavior](https://man7.org/linux/man-pages/man2/PR_SET_CHILD_SUBREAPER.2const.html),
but this does not by itself prove a complete owned-session enumeration.

## Remaining drain limitation

The leader anchor prevents the session ID from being recycled while it is
held, but **does not freeze members or make `/proc` enumeration atomic**.
One possible race is that a session descendant forks while the final `/proc`
listing is being obtained, then exits before its own entry is inspected; the
new child may not be present in that listing. An empty `others` result and a
zombie leader therefore do not alone prove that no live session descendant
remains. Signal handlers or other concurrent behavior can make this relevant.
The current tests do not force that interleaving, and the prototype's README
correctly disclaims a complete enumeration proof and arbitrary adversarial
workloads. A production design needs an appropriate containment or drain
strategy and an explicit, testable statement of the workloads it covers.

The `observed` set stores numeric PIDs and later calls `waitpid` on them. A
reused PID belonging to an unrelated child could be reaped if such children
are created concurrently; the prototype expressly assumes a dedicated
supervisor with no unrelated concurrently created children. It does not
force PID reuse or prove behavior under concurrent reapers, PID-namespace
changes, deliberate session escape, or supervisor SIGKILL. An exception in
the prototype's own fallback cleanup can also prevent complete cleanup or
restoration of subreaper state; its README explicitly disclaims an
exception-safe production implementation. Sampled resource spikes and
production memory, disk, timeout and provider guards are not covered.

## Reproduced and additional controls

The frozen author test exited 0 and reproduced its stored four synthetic
results: monitor exception, leader exit, timeout and injected signal error.
Each reported descendants reaped before the leader; the separate-session
bystander survived, and the injected error remained recorded. These tests
are finite observations, not a proof of complete session cleanup. In an
independent two-child control, the review opened both `/proc` directories,
signaled one child through its descriptor, reaped it, and confirmed that
signaling through its retained old descriptor returned `ESRCH` while the
other session's child was still alive. It did not force PID reuse.

Run [the independent checker](check.py) with:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/nine-variable-anchored-pidfd-supervisor-independent/check.py
```

Its [result](result.json) records the reproduced prototype controls, source
pin check and stale-handle/bystander observation. It creates only temporary
Python sessions; no numeric kill fallback, real gate or Lean process is used.

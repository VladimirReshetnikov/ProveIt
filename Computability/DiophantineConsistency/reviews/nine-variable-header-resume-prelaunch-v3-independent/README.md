# Independent v3 prelaunch review

**The v3 relative-path correction and the supplied synthetic controls pass;
the runner is not approved here for a production traversal.** The exact
13-file revision is frozen under [snapshot](snapshot/) and pinned by
[snapshot-hashes.json](snapshot-hashes.json). No real review gate, header
traversal, Lean reader or project worker was started in this review. The
worker, launcher, core and supervisor hashes match those reported by the
revision author. The v1 and v2 reviews remain separate historical records.

The worker now resolves each parent argv entry relative to the live parent's
`/proc/<pid>/cwd` before comparing it with the expected launcher path. An
independent [fake-repository handshake control](check_wrapped_handshake.py)
reproduces **both absolute and relative invocations** through the actual
`ionice → nice → Python worker` wrapper. Each reaches the expected rejection
of a deliberately mismatched synthetic inventory before that helper runs.
The fake gate exists only in a temporary fake repository. Its recorded
[result](result.json) is not a real approval receipt.

The v3 launcher, queue core and supervisor are byte-identical to the reviewed
v2 versions. The revised worker and test add the launcher-path correction;
README and recorded synthetic results also changed. All four provided
synthetic suites were rerun successfully: queue/checkpoint controls,
128-seed baseline preflight, session/cleanup controls, and fake worker-gate
checks. The read-only [pinned-input check](../nine-variable-header-resume-prelaunch-v2-independent/check_pinned_inputs.py)
also matched all six declared external input hashes and 1,212 project-source
hashes and confirmed 128 distinct declared seeds. The seed replay covers the
64 recorded baseline modules and 199-name frontier plus all declared seeds
in the 287-name starting queue or seen set; it does not perform the pending
header traversal or establish a combined Lean import.

The earlier fixes remain present: the worker checks its one-use pipe, gate,
parent and session before loading the inventory; the helper bytes are
checked before import; each checkpoint is replayed and linked transitions
must preserve its prior processed records, artifacts, namespace observations
and roots; and cleanup records per-member signal failures while continuing,
with subreaper restoration in a nested `finally`. These are workflow and
point-in-time checks with the non-adversarial and transient-substitution
qualifications stated in the author README. Hash-linked local receipts are
not signatures or a proof of reviewer identity. The four synthetic suites
do not prove all OS or provider behaviors.

**The numeric-PID/session signaling race remains.** The v3 supervisor still
observes numeric process IDs and later uses numeric `kill`/`killpg`; a member
or session identifier could be reused in between, potentially signaling an
unrelated process. The revised README expressly records this as an unresolved
risk and does not claim identity-safe signaling. The separate
[anchored proc-descriptor prototype review](../nine-variable-anchored-pidfd-supervisor-independent/README.md)
tests a possible mitigation but is not integrated here and itself retains an
unresolved dynamic-session-enumeration/drain issue. A real batch requires an
appropriate reviewed solution or an explicit, informed acceptance of the
remaining risk; this audit creates neither an approval nor a PASS gate.

The existing RSS/memory/disk checks are sampled and can miss short spikes.
The disk floor is measured on the work directory, which may differ from the
filesystem used by temporary files. Dynamic loading, alternate providers,
namespace changes, deliberately escaped sessions and machine/supervisor
failure retain the limitations in the author packet.

Reproduce the independent handshake with:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/nine-variable-header-resume-prelaunch-v3-independent/check_wrapped_handshake.py
```

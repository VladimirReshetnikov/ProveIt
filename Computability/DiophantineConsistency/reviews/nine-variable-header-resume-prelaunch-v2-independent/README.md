# Independent v2 prelaunch review: two limitations remain

The four concrete findings in the [initial review](../nine-variable-header-resume-prelaunch-independent/README.md)
were addressed in the v2 source. This review does **not** issue a PASS gate or
authorize a header traversal: v2 rejects an otherwise valid relative-path
launcher invocation, and the numeric-PID signaling race remains. The exact
reviewed 13-file revision is retained under [snapshot](snapshot/), with its
[hash manifest](snapshot-hashes.json); this report concerns those bytes only.

## V2 findings

1. **A relative launcher path fails worker authentication.** The worker
   requires `/proc/<parent>/cmdline` to contain the exact absolute path
   `here/launch.py`. A valid launcher invoked with a relative argument has a
   relative argv entry, so the worker rejects it. The independent
   [wrapped handshake control](check_wrapped_handshake.py) reproduces this in
   a temporary fake repository using the actual `ionice → nice → worker`
   chain: an absolute parent path reaches the expected rejection of a
   deliberately mismatched fake inventory, while a relative path is rejected
   by session authentication. No real gate, actual Lean, or header traversal
   is involved. Support relative invocation by safely canonicalizing the
   parent's argv against its cwd and checking the intended file identity, or
   explicitly enforce and document absolute-path invocation before creating a
   run. Retest both forms and preserve the non-adversarial threat scope.

2. **PID reuse can redirect a cleanup signal.** `group_members` reads a
   numeric PID from `/proc`; `drain` later uses `os.kill(pid, ...)` without
   a stable process handle or identity check. If the original process exits,
   is reaped and its PID is reused between those operations, a signal could
   target a different process. The revised per-PID error handling is an
   improvement, but it does not remove this time-of-check/time-of-use race.
   This was found by source inspection, not induced against real processes.
   An identity-bound mechanism such as a pidfd, with the captured identity
   and session verified against the opened handle, is preferable. If retained,
   the limitation needs an explicit risk decision and accurate documentation;
   checking `/proc` immediately before numeric `kill` alone does not close
   the race.

## Initial findings rechecked

* Direct worker execution now checks for a gate and inherited one-use pipe,
  verifies its session and parent, and only then checks the inventory's pinned
  bytes before importing it. The synthetic worker-gate test passed. This is an
  accidental-bypass workflow guard, not a defense against an adversary able
  to control local files or processes.
* The launcher checks gate and code hashes before importing its two helpers;
  the worker checks the inventoried helper's pin before loading it. The
  implementation still reads checked paths again when importing, so transient
  replacement between checks and import is not excluded; the README states
  that assumption. The fake-inventory control confirms an ordinary mismatch
  is rejected before the fake helper executes.
* `validate_chain` replays each ancestor and requires processed-prefix,
  module, artifact, namespace and root continuity. The revised synthetic
  checks reject the prior nonbaseline-record mutation and changed artifact and
  namespace entries. This is a local hash-linked receipt chain, not signed
  provenance.
* `drain` now records per-member signal failures while continuing with other
  members, and `supervise` restores subreaper status in a nested `finally`.
  The synthetic monitor exception, leader exit, timeout, signal-error,
  inspection/group-signal error and subreaper-restoration tests passed. These
  results do not establish cleanup after every OS failure, session escape,
  supervisor SIGKILL, or PID reuse.

All four provided synthetic suites were rerun from the frozen v2 snapshot and
passed; they did not run Lean. Separately, [check_pinned_inputs.py](check_pinned_inputs.py)
verified the six declared external byte pins, all 1,212 project-source hashes
and 128 distinct declared seed names. The static preflight replayed 64 old
modules and the 199-name frontier, then accounted for all 128 names in the
287-name initial queue or visited set. These facts are point-in-time input and
static-header controls, not a source rebuild or combined Lean import. Resource
limits remain sampled; the disk floor is checked on the work directory, and
temporary paths can in general be on a different filesystem.

Run the fake wrapped handshake and the read-only pinned-input verification:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/nine-variable-header-resume-prelaunch-v2-independent/check_wrapped_handshake.py
python3 -I -S -B Computability/DiophantineConsistency/reviews/nine-variable-header-resume-prelaunch-v2-independent/check_pinned_inputs.py
```

The handshake [result](result.json) is scoped to a temporary fake repository
and fake gate. It starts no Lean process and never creates a gate or result in
the actual research run directory.

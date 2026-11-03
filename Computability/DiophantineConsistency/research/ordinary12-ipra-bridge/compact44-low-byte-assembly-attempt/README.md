# Prepared full MC recipe assembly: not yet checked

`CompactLowByteAssembly.lean` is a copy of the independently source-reviewed
assembly draft. The guarded `prepare.py` run selected the corrected
single-case boundary-01 source and receipt rather than the warning-rejected
original, checked all 12 boundary sources, objects, logs and current direct
guards, pinned the other selected objects, and constructed a fresh
single-root union. It recorded 606 selected files, no conflicting shared
file hashes and no suppressed foreign companions, with selected provider
inventories unchanged. The full point-in-time manifest is retained at
`observations/prepare-attempt01/manifest.json`.

The bounded mixed-provider Lean attempt at `observations/attempt01` **failed**
at the default 200,000-heartbeat limit in the gap branch's `split_ifs`/`omega`
proof and the enclosing `point` theorem. It produced no output object. The
error-recovery `sorryAx` report is not a proof. Exact source, log, dependency
guards and receipt are retained; direct guards, selected union files and
previously inventoried provider files remained unchanged. A separate
subsequent retry will isolate the costly sublemmas and increase the heartbeat
limit under the same memory and wall-clock caps. No MC assembly theorem is
established by this attempt.

Neither this plan nor a future successful symbolic assembly establishes the
file/gzip-to-Lean correspondence, parent-to-supplement provenance, a PDF or
an iPRA endpoint. Complete project/package/dynamic ancestry and paired replay
would remain separate audit obligations even after an author build.

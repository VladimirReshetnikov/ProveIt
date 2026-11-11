# K215 forward 09 split guard

This isolated 23-stage build recompiles the full 20-stage K215 compatibility provider, independently checks the two actual root children of `fwd9`, and joins them into the unchanged original-namespace `fwd_ok9` statement. The original project files remain untouched. Both KSource215Data and KSource215FwdCheck09 here are source-level proof refactors, not byte-identical originals. The full coherent rebuild and package/dynamic ancestry remain separate.

Caps unchanged: sampled 4 GiB RSS, `lean -M3600 -j1 -DElab.async=false`, 180 seconds per child, 10 GiB host memory, 5.1 GB sampled disk stop, and six-hour global trigger. Forced receipt, log hashing and cleanup may finish later. No preexisting files are removed. Controls/preflight do not launch Lean; independent review and allocated slot required.

Attempt01 failed: outer session 15080 exited 1 at the join after both child checks passed. Rewriting left `(true && true) = true` unsolved; the join has no object or postflight. The [independent failure audit](../../reviews/current14-k215-fwd09-split-failure-independent/) verifies the frozen evidence; no failed-parent result is promoted.

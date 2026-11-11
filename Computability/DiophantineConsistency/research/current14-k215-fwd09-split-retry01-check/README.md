# K215 forward 09 split retry

This fresh 23-stage run recompiles the full compatibility provider, both original split subchecks and a join retry with a single `rfl` added after rewriting. The failed parent is retained; none of its objects is reused. The original project files remain untouched; KSource215Data and FwdCheck09 are source-level proof refactors. Full coherent rebuild and package/dynamic ancestry remain separate.

Caps remain 4 GiB sampled RSS, `lean -M3600 -j1 -DElab.async=false`, 180 seconds per child, 10 GiB host memory, 5.1 GB sampled disk stop and six-hour global trigger. Forced receipt and cleanup can finish later. No preexisting files are removed. Controls and preflight do not run Lean; independent review and slot allocation are required.

Attempt01 passed: outer session 12713 exited 0, all 23 stages and postflight passed. The [independent terminal audit](../../reviews/current14-k215-fwd09-split-retry01-terminal-independent/) verified the child and original-statement join reports and provider routes. The full coherent rebuild remains separate.

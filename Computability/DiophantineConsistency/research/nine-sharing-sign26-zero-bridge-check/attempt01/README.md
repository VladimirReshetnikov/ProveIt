# Sign26 zero-bridge attempt 01: partial failure

Author-observed outer session 55449 exited 1. CoordinateDrop and ForwardBridge compiled successfully; ReverseBridge failed. The reverse compilation reports deterministic 200,000-heartbeat `whnf` timeouts at 51:4 and 34:58, followed by unknown `backward`. The printed `new_rows` report occurred during a failed compilation and does not establish a reverse object or theorem. Final postflight did not run. The precise reduction causing the timeouts is not established.

CoordinateDrop reports `lift_drop` and `drop_lift` with `[propext, Classical.choice, Quot.sound]`, plus two unused section-variable warnings. ForwardBridge reports `old_rows` with `[propext]` and `forward` with `[propext, Classical.choice, Quot.sound]`, with no warnings. Forward retains explicit p0/p1 casts and beta bound. The two successful stage objects and logs are pinned by state.json; they are not a complete zero-set equivalence. Monitor sampling is not a complete trace.

Historical caveat: the sign26 plan README was appended with its audit link after its source audit; the original audit checker pins the earlier bytes and cannot replay verbatim without removing that documentation addition. This does not alter the Lean source.

# Sign22 same-input zero existence guarded check

This one-stage candidate proposes same-input sign22/sign23 seed zero existence
equivalence under arbitrary symbolic ports in IΣ₁ models. The natural kY lift
introduces no beta-port representation premise. It composes the captured
forward/reverse zero assembly; the direct expression and iPRA endpoint remain
separate.

The runner checks the captured two-stage assembly's source, objects, logs,
direct guards and overlay links, and source and manifest pins. These are
point observations, not a full transitive or dynamic ancestry trace. It uses
`-M2800`, one thread and a 120-second timeout per Lean invocation, a monitored
4 GiB RSS cap, 10 GiB available-memory floor and 5 GB disk precheck. The
upstream syntax provider inherits the 4,000,000-heartbeat option; this client
adds none.

Author no-Lean preflight exited 0 (`preflight-author-record.json`). The
assembly producer passed independent terminal audit. After independent
prelaunch review, attempt 01 passed with author-observed outer session `18840`
exit 0; see `attempt01/README.md`. The [independent terminal audit](../../reviews/nine-sharing-sign22-seed-iff-terminal-independent/README.md)
passed; the packet and stage input are frozen.

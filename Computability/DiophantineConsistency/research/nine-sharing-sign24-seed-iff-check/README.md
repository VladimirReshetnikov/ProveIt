# Sign24 same-input zero existence guarded check

This single-stage candidate proposes same-input sign24/sign25 seed zero
existence equivalence over symbolic ports, retaining the explicit model-natural
beta representation. It composes the forward/reverse zero assembly and the
coordinate maps; current-port specialization and an iPRA endpoint are
separate.

The runner audits the captured two-stage zero assembly's source, objects,
logs, direct guards and overlay links, and checks the input source and manifest
pins. These are point observations, not a full transitive or dynamic ancestry
trace. It uses the same `-M2800`, one-thread, 120-second Lean invocation,
4 GiB monitored RSS, 10 GiB available-memory floor and 5 GB free-disk check
as its predecessor. The upstream syntax provider inherits the 4,000,000
heartbeat option; this client does not add one.

Author no-Lean preflight exited 0 (`preflight-author-record.json`). After
independent assembly terminal and client prelaunch audits, attempt 01 passed
with author-observed outer session `75452` exit 0. See `attempt01/README.md`;
the [independent terminal audit](../../reviews/nine-sharing-sign24-seed-iff-terminal-independent/README.md)
passed, and the packet and stage input are frozen. Current-port result, byte
binding and iPRA endpoint remain separate.

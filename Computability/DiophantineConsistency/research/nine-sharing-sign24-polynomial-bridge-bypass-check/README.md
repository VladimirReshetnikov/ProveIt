# Sign24 polynomial bridge via sign26: guarded candidate

This single-stage candidate composes the audited sign24↔sign25 and
sign25↔sign26 model-zero equivalences, then transports the checked sign26
polynomial bridge directly. It avoids importing the sign25 concrete bridge.
The proposed provider union has, respectively, 1,058/1,064/1,058 base
overlaps and 20/14/307 extra entries for generic transport, sign25 expression
iff and sign26 concrete bridge. Shared extra bytes are checked on injection.
The union checks source, object, logs, direct dependency guards and overlay
observations; they are not a complete transitive or dynamic ancestry trace.

Two prior sign24 attempts failed with interpreter memory exceptions under
`-M2800`; the staged retry did compile its conditional first stage. This
candidate changes the import and elaboration route but uses the same
`-M2800`, one-thread and 120-second limits, 4 GiB monitored RSS, 10 GiB
available-memory floor and 5 GB disk precheck. It does not add a heartbeat
option; the syntax provider inherits the 4,000,000-heartbeat setting.

Author no-Lean preflight exited 0 (`preflight-author-record.json`). After
independent prelaunch review, attempt 01 failed with author-observed outer
session `33816` exit 1 due to an interpreter memory exception; see
`attempt01/README.md`. The [independent failure audit](../../reviews/nine-sharing-sign24-polynomial-bridge-bypass-terminal-independent/README.md)
passed; the packet and stage input are frozen. No new polynomial bridge,
iPRA endpoint, Lean degree theorem or external-file binding follows.

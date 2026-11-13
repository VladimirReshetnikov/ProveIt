# Sign24 forward/reverse zero assembly guarded check

This two-stage candidate proposes the sign24→sign25 forward zero map and
reverse zero map, using the checked q3 coordinate recovery and 15 audited
residual-transfer identities. Both claims retain the explicit symbolic
beta-port representation hypothesis in an IΣ₁ model. The first stage
enumerates all 16 old rows; the second enumerates all 15 new rows.

The runner uses the captured three-stage sign24 transfer base, checks each
producer source, object, logs, direct guards and overlay links, pins source
copies, generator and manifest, and routes each import to its producer.
It checks snapshots rather than complete transitive or dynamic ancestry.
It uses `-M2800`, one thread and a 120-second timeout per Lean invocation,
with 4 GiB monitored RSS and a 10 GiB host-memory floor, and checks for 5 GB
free disk before launch. The inherited syntax provider has a 4,000,000
heartbeat option; these assembly sources do not add one.

The author no-Lean preflight exited 0; see `preflight-author-record.json`.
After independent prelaunch review, attempt 01 passed with author-observed
outer session `4281` exit 0; see `attempt01/README.md`. Independent terminal
audit passed at [the independent review](../../reviews/nine-sharing-sign24-zero-assembly-terminal-independent/README.md);
the packet and stage inputs are frozen. Current-port specialization, Lean/JSON binding, degree
theorem and iPRA endpoint remain separate.

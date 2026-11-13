# Sign23 transfer numeral-rewrite retry

This fresh-output two-stage retry adds `map_ofNat` to the simp list of every
one of the 14 evaluation identities, targeting the recorded failed numeral
embeddings. The first attempt failed in `Dc2_eval` with `sorryAx`; its second
stage did not run. No failed declaration is credited as a proof.

The guard retains the same coordinate-retry base and author-side AST/offset
receipt. It uses the same `-M2800`, one-thread, 120-second invocation limits,
monitored 4 GiB RSS cap, 10 GiB host-memory floor and 5 GB disk precheck.
Source snapshots and provider guards are point observations, not complete
transitive or dynamic ancestry; the syntax provider retains its inherited
4,000,000-heartbeat option. The author no-Lean preflight passed
(`preflight-author-record.json`). The prior failure passed independent audit.
After independent prelaunch review, retry attempt 01 passed with author-observed
outer session `59493` exit 0; see `attempt01/README.md`. Independent terminal
audit passed at [the independent review](../../reviews/nine-sharing-sign23-transfers-retry01-terminal-independent/README.md);
the packet and stage inputs are frozen.

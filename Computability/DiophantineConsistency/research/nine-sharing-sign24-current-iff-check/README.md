# Sign24 current-port seed equivalence guarded check

This single-stage candidate specializes sign24/sign25 same-input zero
existence equivalence to the current ports. It checks that the beta port is the
model-natural cast of `CurrentMasks2011.beta`, using the same proof as the
checked sign28 specialization. It does not yet supply a direct expression,
an iPRA endpoint, or a binding of the external coefficient bytes to Lean.

The runner adapts the sign28 current-port guard, checking the sign24
same-input base and direct guards and surveying the current-data provider.
The current-data observation is inherited from successful individual stages
of a producer whose overall run failed; it is not credit for a successful
producer run. Its deeper ancestry, point-observation scope and sampled-monitor
limits are inherited. Each Lean invocation uses `-M2800`, one thread and
120 seconds, with a 4 GiB monitored RSS cap, 10 GiB host-memory floor and
5 GB free-disk precheck. The upstream sign24 syntax option remains 4,000,000
heartbeats; no new heartbeat option is added here.

The author no-Lean preflight exited 0 (`preflight-author-record.json`). The
same-input producer has passed independent terminal audit. This candidate
passed after independent prelaunch review, with author-observed outer session
`62455` exit 0; see `attempt01/README.md`. Independent terminal audit is
complete at [the independent review](../../reviews/nine-sharing-sign24-current-iff-terminal-independent/README.md);
the packet and stage input are frozen.

# Sign23 Delta lift and recovery guarded check

This single-stage candidate proposes the natural polynomial lift and drop,
old Delta zero on the lift, recovery of coordinate 18 from old sign24 seed
zero, and `lift (drop v) = v` under that hypothesis. No beta representation
assumption is required for this substitution. The client does not check the
14 remaining residual transfers, an assembled bridge, or an iPRA endpoint.

The runner adapts the sign24 coordinate guard. It uses the sign23
syntax/squares attempt as base and surveys both sign24 producer rows and
their shared direct dependency paths before a new overlay is built. It checks
source, object, log and direct provider observations, not a complete
transitive or dynamic ancestry trace. Lean invocations use `-M2800`, one
thread and 120 seconds, with a monitored 4 GiB RSS cap, 10 GiB host-memory
floor, and 5 GB free-disk precheck. The syntax provider retains the inherited
4,000,000-heartbeat option; no new heartbeat option is added here.

Author no-Lean preflight exited 0 (`preflight-author-record.json`). After
independent prelaunch review, attempt 01 failed with author-observed outer
session `90674` exit 1 due to an unsolved numeral-embedding goal. Its failed
theorem's report includes `sorryAx`; see `attempt01/README.md`. Independent
failure audit passed at [the independent review](../../reviews/nine-sharing-sign23-coordinate-terminal-independent/README.md);
the packet and stage input are frozen. No coordinate theorem is claimed from
this run.

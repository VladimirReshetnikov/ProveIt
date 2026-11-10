# Sign24 q3 lift and recovery guarded check

This one-stage proposal checks the beta-parametric product lift and drop,
old q3 zero on the lift, recovery of old coordinate 15 from an old seed zero,
and `lift (drop v) = v` under that hypothesis. It explicitly assumes
`((p 0 : ℤ) : DiffRing V) = ι beta` for the given model and symbolic ports.
It does not check any of the 15 retained residual transfers or an assembled
zero equivalence, a current-ports specialization, or an iPRA endpoint.

The runner adapts the guarded sign25 first-cut runner. It uses the sign24
syntax/squares attempt as base and surveys both independently audited sign25
syntax/squares producer rows and their shared direct dependency paths before
injecting them into a new overlay. It pins the exact source copy and manifest,
and guards direct dependencies at each stage; these are point observations,
not a transitive or dynamic ancestry trace. It inherits the 4,000,000-heartbeat
option from the sign24 syntax provider; the stage itself has no changed
heartbeat setting. Lean uses `-M2800`, one thread and a 120-second limit, with
4 GiB monitored RSS, a 10 GiB host-memory floor and 5 GB disk precheck.

The author no-Lean preflight exited 0; see `preflight-author-record.json`.
After independent prelaunch review, attempt 01 passed with author-observed
outer session `6572` exit 0; see `attempt01/README.md`. Independent terminal
audit passed at [the independent review](../../reviews/nine-sharing-sign24-coordinate-terminal-independent/README.md).
The packet and its stage input are frozen.

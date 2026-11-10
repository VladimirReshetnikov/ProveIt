# Sign25 wrappers over an audited partial native producer

Two candidate wrapper stages use the native object from a previously failed
outer run whose native child compiled and was independently audited. The runner
rechecks that exact partial producer, its source, direct guards, logs, object
and overlays, with same resource limits and fresh output. No successful full
producer postflight is claimed. Author no-Lean preflight exited 0; independent
review is required and Lean may run only on an assigned slot. Runner SHA-256
`80c080da95b678b1ed3d56ad047d040a73752ab4b0f995345d9455abfff45cd6`;
manifest SHA-256
`a3c2e0a8d69877c4c4179e271d26e98bfc96e26c870f3768eca6469f1546ad46`.

Attempt 01 failed in the first standard wrapper; see
[`attempt01`](attempt01/README.md). Its [independent prelaunch review](../../reviews/nine-sharing-sign25-endpoint-wrappers-prelaunch-independent/README.md)
and [terminal audit](../../reviews/nine-sharing-sign25-endpoint-wrappers-terminal-independent/README.md)
record the inputs and failure.

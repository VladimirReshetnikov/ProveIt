# Sign25 wrapper import diagnostic guarded client

Three import-only diagnostic stages use a native object from a previously failed
outer run whose native child compiled and was independently audited. The runner
rechecks that exact partial producer, its source, direct guards, logs, object
and overlays, with same resource limits and fresh output. No successful full
producer postflight is claimed. Author no-Lean preflight exited 0; independent
review is required and Lean may run only on an assigned slot. Runner SHA-256
`494fe3e9e62f725aea06438b5d12311b111c48721d2928e5fc1c098399167a82`;
manifest SHA-256
`1f178eaebf7e0e0361c3c03310979f973a5c73b3ce652fde7202336bbfda6e80`.

Attempt 01 compiled native-only, standard-only and combined import modules,
with observed outer exit 0; see [`attempt01`](attempt01/README.md). The
[independent prelaunch review](../../reviews/nine-sharing-sign25-wrapper-import-diagnostic-prelaunch-independent/README.md)
and [terminal audit](../../reviews/nine-sharing-sign25-wrapper-import-diagnostic-terminal-independent/README.md)
record the inputs and result. This does not establish an endpoint.

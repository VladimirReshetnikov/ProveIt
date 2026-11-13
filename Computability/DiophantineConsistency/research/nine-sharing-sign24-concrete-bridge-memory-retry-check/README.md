# Sign24 concrete bridge scoped memory retry

This source-only retry uses the identical source, manifest and provider union as
the previously failed sign24 bridge, with Lean interpreter limit increased from
`-M2800` to `-M3600`. The existing 4 GiB sampled RSS cap, 10 GiB host-memory
floor, 120-second timeout, disk precheck and provider guards are unchanged.
No theorem is claimed pending Lean and independent terminal audit. Author
no-Lean preflight session `58228` exited 0. Runner SHA-256:
`b35611bbc283834f6c0ab17338385a1bc31ff30d30ae5609ab382b489df443a4`;
manifest SHA-256:
`0a6775382f22779bf38bd541909192f941e57ec95c07b39f2522c461f7d5b9f9`.
An independent prelaunch review and assigned Lean slot are required.

Attempt 01 compiled the bridge and passed final postflight, with observed outer
exit 0; see [`attempt01`](attempt01/README.md). The retained stdout incorrectly
says sign25. The [independent prelaunch review](../../reviews/nine-sharing-sign24-concrete-bridge-memory-retry-prelaunch-independent/README.md)
and [terminal audit](../../reviews/nine-sharing-sign24-concrete-bridge-memory-retry-terminal-independent/README.md)
record the checked result. No iPRA endpoint or external JSON/PDF binding is
claimed.

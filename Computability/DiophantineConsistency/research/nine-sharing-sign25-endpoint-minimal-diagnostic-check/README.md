# Sign25 minimal endpoint diagnostic guarded client

Three source-only stages independently test a command, expression alias and
local attributes after the earlier memory failures.
The runner is adapted from the pinned endpoint runner with the same resource
limits and independent output directory; the diagnostic changes import
boundaries and therefore does not by itself isolate the exact original cause.
No endpoint is claimed. Author no-Lean preflight exited 0 for three stages;
independent review is required, and Lean may run only on an assigned slot.
The runner SHA-256 is
`42413377214db7f883673e6e821bc96256c11b6f15013b396d4e5bd9752f2c97`;
the manifest SHA-256 is
`f8995a2b813e5ec16681539b6a28670459f806752370995ea1e7bc376e5ac65e`.

Attempt 01 failed in the alias-only stage after a successful bridge `#check`;
see [`attempt01`](attempt01/README.md). The [independent prelaunch review](../../reviews/nine-sharing-sign25-endpoint-minimal-diagnostic-prelaunch-independent/README.md)
and [terminal audit](../../reviews/nine-sharing-sign25-endpoint-minimal-diagnostic-terminal-independent/README.md)
record the checked inputs and result.

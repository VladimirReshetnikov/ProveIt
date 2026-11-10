# Sign25 split endpoint diagnostic guarded client

Four source-only stages separately test the bridge import, expression alias,
bridge theorem and axiom report after the original first-stage memory failure.
The runner is adapted from the pinned endpoint runner with the same resource
limits and independent output directory; the diagnostic changes import
boundaries and therefore does not by itself isolate the exact original cause.
No endpoint is claimed. Author no-Lean preflight exited 0 and reports four
stages. Independent review is required, and Lean may run only on an assigned
slot. The source draft and runner generator are in the corresponding
`nine-sharing-sign25-endpoint-diagnostic-draft` directory. The runner SHA-256
is `213c1ca053ba8a44e8af4378e1bbb92e22967f1f96745f957919cf26f4eae7cf` and
the manifest SHA-256 is
`4e60a3e4a25c56aeaf6251979ba5321188b85d58bf8891df5a95fdd9ddc564ea`.

Attempt 01 failed after compiling the import-only stage; see
[`attempt01`](attempt01/README.md) for the captured second-stage interpreter
exception and scope. The [independent prelaunch review](../../reviews/nine-sharing-sign25-endpoint-diagnostic-prelaunch-independent/README.md)
and [terminal audit](../../reviews/nine-sharing-sign25-endpoint-diagnostic-terminal-independent/README.md)
record the checked inputs and result.

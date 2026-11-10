# Sign25 no-alias endpoint guarded client

Three source-only stages apply the existing bridge directly to native,
standard and translated endpoints without a new expression alias.
The runner is adapted from the pinned endpoint runner with the same resource
limits and independent output directory; the diagnostic changes import
boundaries and therefore does not by itself isolate the exact original cause.
No endpoint is claimed. Author no-Lean preflight exited 0 for three stages;
independent review is required, and Lean may run only on an assigned slot.
Runner SHA-256:
`d36f5bd20ed4f8d7a6a414f309a499d2520c94493ffa3e78ba7e7f0e3aae4ccd`.
Manifest SHA-256:
`2952924dc5c8323f8ae0a6fd5ed112b22d8648843b91a9bcb8c3b6e7d7ff69fc`.

Attempt 01 compiled the native theorem, then failed the standard stage with
an interpreter memory exception; see [`attempt01`](attempt01/README.md). The
outer run failed and final postflight did not run. The [independent prelaunch
review](../../reviews/nine-sharing-sign25-endpoint-no-alias-prelaunch-independent/README.md)
and [partial terminal audit](../../reviews/nine-sharing-sign25-endpoint-no-alias-terminal-independent/README.md)
record the successful native child and standard-stage failure.

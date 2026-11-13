# Sign25 pretyped-assertion endpoint guarded client

Four source-only stages compile a generic endpoint, pretyped assertion,
a typed endpoint, and the original-sentence wrapper.
The runner is adapted from the pinned endpoint runner with the same resource
limits and independent output directory; the diagnostic changes import
boundaries and therefore does not by itself isolate the exact original cause.
No endpoint is claimed. Author no-Lean preflight exited 0 for four stages;
independent review is required, and Lean may run only on an assigned slot.
Runner SHA-256:
`516b079b448dc30a15ebe292eacfc4d72062185753a6b71ee7febb6ea32d1a7f`.
Manifest SHA-256:
`5f61aacbe7ad832e2d4129289c3c40c9e29325fffeb025c82b6a721bf6b2863a`.

Attempt 01 compiled the generic theorem and full typed assertion, then failed
specialization; see [`attempt01`](attempt01/README.md). Overall exit was 1 and
final postflight did not run. The [independent prelaunch review](../../reviews/nine-sharing-sign25-pretyped-assertion-prelaunch-independent/README.md)
and [partial terminal audit](../../reviews/nine-sharing-sign25-pretyped-assertion-terminal-independent/README.md)
record the checked prefix and failure.

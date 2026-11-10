# Sign25 pretyped-sentence endpoint guarded client

Four source-only stages compile a generic endpoint, a pretyped sentence,
a typed endpoint, and the original-sentence wrapper.
The runner is adapted from the pinned endpoint runner with the same resource
limits and independent output directory; the diagnostic changes import
boundaries and therefore does not by itself isolate the exact original cause.
No endpoint is claimed. Author no-Lean preflight exited 0 for four stages;
independent review is required, and Lean may run only on an assigned slot.
Runner SHA-256:
`1f44f4c97ea3c4c14bf1200abf9b4da68cab9925d589934dc13ebf8f09afc10e`.
Manifest SHA-256:
`d5900df9d85ad04c8913ea7bad3175ea32c3c7898f223b501300c8f1431bae3f`.

Attempt 01 compiled the generic theorem and typed sentence, then failed the
typed bridge specialization; see [`attempt01`](attempt01/README.md). Overall
exit was 1 and final postflight did not run. The [independent prelaunch review](../../reviews/nine-sharing-sign25-typed-sentence-prelaunch-independent/README.md)
and [partial terminal audit](../../reviews/nine-sharing-sign25-typed-sentence-terminal-independent/README.md)
record the two successful children and later failure.

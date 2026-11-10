# Sign25 typed-specialization diagnostic guarded client

Five source-only stages compile generic and typed-sentence declarations then
test the heavy imports, the assertion and the specialized proof term.
The runner is adapted from the pinned endpoint runner with the same resource
limits and independent output directory; the diagnostic changes import
boundaries and therefore does not by itself isolate the exact original cause.
No endpoint is claimed. Author no-Lean preflight exited 0 for five stages;
independent review is required and Lean may run only on an assigned slot.
Runner SHA-256:
`aed65d2aa512dcea9c415c0bed978d97a037074c9b9c57f1c7fefb0cb60a4609`.
Manifest SHA-256:
`8157af08b12439d7b10feac73515e80af0ce54402e22fa0f8856d12bc9823161`.

Attempt 01 compiled the first three stages and failed in the assertion-check
module; see [`attempt01`](attempt01/README.md). Overall exit was 1 and final
postflight did not run. The [independent prelaunch review](../../reviews/nine-sharing-sign25-specialization-diagnostic-prelaunch-independent/README.md)
and [partial terminal audit](../../reviews/nine-sharing-sign25-specialization-diagnostic-terminal-independent/README.md)
record the checked prefix and failure.

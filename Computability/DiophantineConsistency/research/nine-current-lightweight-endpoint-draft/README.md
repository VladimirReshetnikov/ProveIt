# Draft nine-variable endpoint on the lightweight Jones bridge

This **uncompiled draft** adapts `IPRANineCurrent` by using the generic `NineLightQuartic` model bridge and the checked `HACurrentEquation2011.polynomialBridge` directly. It retains the original nine-coordinate Jones expression and its intended native and standard iPRA equivalences, and omits the equality-only endpoint to avoid importing that separate proof-conversion closure. The lightweight `ModelJonesNine` source adaptation is still being checked separately; this draft is not a proved theorem or an authenticated equation-size result.

The draft is a distinct source variant and must be compiled against source-pinned, independently reviewed providers. A successful proof would still require a separate correspondence between its abstract `ExecutableJones.expression seed 0` syntax and any displayed equation or size estimate. No such graph binding or degree count is asserted here.

Attempt01 was run and failed: actual outer session 55005 exited 1, and Lean exited 1 on missing `NatExpr.rename` and the current-bridge type. Its captured source, logs and state are in `attempt01/`; it contains `sorryAx` in failed elaboration output. The corrected [attempt02](../nine-current-lightweight-endpoint-retry/README.md) subsequently passed.

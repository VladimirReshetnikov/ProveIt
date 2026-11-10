# Sign25 endpoint attempt 01: failure

The observed outer runner session `63793` exited **1**. The first stage,
`Sign25NativeExpression`, had dependency inspection exit 0, then Lean compile
exit -6 with a `lean::memory_exception` at the interpreter under `-M2800`.
The monitor recorded no stop reason or errors, a sampled peak session RSS of
2,938,626,048 bytes and minimum host availability of 19,518,787,584 bytes.
Those sampled readings do not rule out transient spikes. No endpoint object
or final postflight was produced; later stages did not run. The precise cause
of the interpreter exception is unknown.

The runner's retained state `scope` says sign26, a stale label: the pinned
source, manifest and attempted module are sign25. This result inherits the
sign26 ancestry and previously documented provider, heartbeat and earlier
stale-label qualifications. The captured logs and `state.json` are copied
from the isolated `/tmp` attempt; `outer-result.json` separately records the
actual session exit rather than inferring it from a child status. The
[independent failure audit](../../../reviews/nine-sharing-sign25-endpoint-terminal-audit-20261109/README.md)
checks the retained output, source pins, guards and links.

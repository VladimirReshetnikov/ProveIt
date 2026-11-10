# Sign24 concrete bridge, attempt 01: failure

The author observed numeric outer session `56027` exit 1. Dependency
inspection succeeded, but compiling `Sign24DirectPolynomialBridge` exited
`-6` with a Lean interpreter `memory_exception` under `-M2800`. No bridge
object or final postflight was produced. The sampled monitor recorded no
stop reason, a peak session RSS of 2,939,170,816 bytes and minimum host
availability of 19,477,737,472 bytes; these observations may miss transient
spikes. The precise cause of the interpreter exception is unknown.

The terminal state and two stage logs are frozen here, and `outer-result.json`
records the author-observed numeric outer exit separately from the child
status. Independent failure audit requested. The point-observed provider and
inherited ancestry qualifications remain. The retained runner state scope
incorrectly says sign25; the pinned source and attempted module are sign24.
